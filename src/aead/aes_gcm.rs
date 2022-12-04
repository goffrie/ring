// Copyright 2015-2016 Brian Smith.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHORS DISCLAIM ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

use super::{
    aes::{self, Counter},
    block::{Block, BLOCK_LEN},
    gcm, Aad, Nonce, Tag,
};
use crate::{aead, cpu, error, polyfill};
use core::{ptr, slice};

/// AES-128 in GCM mode with 128-bit tags and 96 bit nonces.
pub static AES_128_GCM: aead::Algorithm = aead::Algorithm {
    key_len: 16,
    init: init_128,
    seal: aes_gcm_seal,
    open: aes_gcm_open,
    id: aead::AlgorithmID::AES_128_GCM,
    max_input_len: AES_GCM_MAX_INPUT_LEN,
};

/// AES-256 in GCM mode with 128-bit tags and 96 bit nonces.
pub static AES_256_GCM: aead::Algorithm = aead::Algorithm {
    key_len: 32,
    init: init_256,
    seal: aes_gcm_seal,
    open: aes_gcm_open,
    id: aead::AlgorithmID::AES_256_GCM,
    max_input_len: AES_GCM_MAX_INPUT_LEN,
};

#[derive(Clone)]
pub struct Key {
    gcm_key: gcm::Key, // First because it has a large alignment requirement.
    aes_key: aes::Key,
}

fn init_128(key: &[u8], cpu_features: cpu::Features) -> Result<aead::KeyInner, error::Unspecified> {
    init(key, aes::Variant::AES_128, cpu_features)
}

fn init_256(key: &[u8], cpu_features: cpu::Features) -> Result<aead::KeyInner, error::Unspecified> {
    init(key, aes::Variant::AES_256, cpu_features)
}

fn init(
    key: &[u8],
    variant: aes::Variant,
    cpu_features: cpu::Features,
) -> Result<aead::KeyInner, error::Unspecified> {
    let aes_key = aes::Key::new(key, variant, cpu_features)?;
    let gcm_key = gcm::Key::new(aes_key.encrypt_block(Block::zero()), cpu_features);
    Ok(aead::KeyInner::AesGcm(Key { gcm_key, aes_key }))
}

const CHUNK_BLOCKS: usize = 3 * 1024 / 16;

// See the comments on `Algorithm::seal` for the safety invariants of this function.
unsafe fn aes_gcm_seal(
    key: &aead::KeyInner,
    nonce: Nonce,
    aad: Aad<&[u8]>,
    mut plaintext: *const u8,
    mut out_ciphertext: *mut u8,
    mut len: usize,
) -> Tag {
    let Key { gcm_key, aes_key } = match key {
        aead::KeyInner::AesGcm(key) => key,
        _ => unreachable!(),
    };

    let mut ctr = Counter::one(nonce);
    let tag_iv = ctr.increment();

    let aad_len = aad.0.len();
    let mut auth = gcm::Context::new(gcm_key, aad);

    let total_len = len;

    #[cfg(target_arch = "x86_64")]
    if aes_key.is_aes_hw() && auth.is_avx2() {
        use crate::c;
        prefixed_extern! {
            fn aesni_gcm_encrypt(
                input: *const u8,
                output: *mut u8,
                len: c::size_t,
                key: &aes::AES_KEY,
                ivec: &mut Counter,
                gcm: &mut gcm::ContextInner,
            ) -> c::size_t;
        }
        let processed = aesni_gcm_encrypt(
            plaintext,
            out_ciphertext,
            len,
            aes_key.inner_less_safe(),
            &mut ctr,
            auth.inner(),
        );
        assert!(processed <= len);
        (plaintext, out_ciphertext, len) = (
            plaintext.add(processed),
            out_ciphertext.add(processed),
            len - processed,
        )
    };

    const MAX_CHUNK_LEN: usize = CHUNK_BLOCKS * BLOCK_LEN;
    while len > 0 {
        if len >= BLOCK_LEN {
            let chunk_len = if len >= MAX_CHUNK_LEN {
                MAX_CHUNK_LEN
            } else {
                len / BLOCK_LEN * BLOCK_LEN
            };
            aes_key.ctr32_encrypt(plaintext, out_ciphertext, chunk_len, &mut ctr);
            auth.update_blocks(slice::from_raw_parts(out_ciphertext, chunk_len));
            (plaintext, out_ciphertext, len) = (
                plaintext.add(chunk_len),
                out_ciphertext.add(chunk_len),
                len - chunk_len,
            );
        } else {
            // this is a partial block; pad it with zeroes
            let mut plaintext_block = Block::zero();
            plaintext_block.overwrite_part_at(0, slice::from_raw_parts(plaintext, len));
            let mut ciphertext_block = aes_key.encrypt_iv_xor_block(ctr.into(), plaintext_block);
            ciphertext_block.zero_from(len);
            auth.update_block(ciphertext_block);
            ptr::copy_nonoverlapping(
                ciphertext_block.as_ref()[..len].as_ptr(),
                out_ciphertext,
                len,
            );
            break;
        }
    }

    finish(aes_key, auth, tag_iv, aad_len, total_len)
}

// See the comments on `Algorithm::open` for the safety invariants of this function.
unsafe fn aes_gcm_open(
    key: &aead::KeyInner,
    nonce: Nonce,
    aad: Aad<&[u8]>,
    mut ciphertext: *const u8,
    mut out_plaintext: *mut u8,
    mut len: usize,
) -> Tag {
    let Key { gcm_key, aes_key } = match key {
        aead::KeyInner::AesGcm(key) => key,
        _ => unreachable!(),
    };

    let mut ctr = Counter::one(nonce);
    let tag_iv = ctr.increment();

    let aad_len = aad.0.len();
    let mut auth = gcm::Context::new(gcm_key, aad);

    let total_len = len;

    #[cfg(target_arch = "x86_64")]
    if aes_key.is_aes_hw() && auth.is_avx2() {
        use crate::c;

        prefixed_extern! {
            fn aesni_gcm_decrypt(
                input: *const u8,
                output: *mut u8,
                len: c::size_t,
                key: &aes::AES_KEY,
                ivec: &mut Counter,
                gcm: &mut gcm::ContextInner,
            ) -> c::size_t;
        }

        let processed = aesni_gcm_decrypt(
            ciphertext,
            out_plaintext,
            len,
            aes_key.inner_less_safe(),
            &mut ctr,
            auth.inner(),
        );
        assert!(processed <= len);
        (ciphertext, out_plaintext, len) = (
            ciphertext.add(processed),
            out_plaintext.add(processed),
            len - processed,
        )
    };

    const MAX_CHUNK_LEN: usize = CHUNK_BLOCKS * BLOCK_LEN;
    while len > 0 {
        if len >= BLOCK_LEN {
            let chunk_len = if len >= MAX_CHUNK_LEN {
                MAX_CHUNK_LEN
            } else {
                len / BLOCK_LEN * BLOCK_LEN
            };
            auth.update_blocks(slice::from_raw_parts(ciphertext, chunk_len));
            aes_key.ctr32_encrypt(ciphertext, out_plaintext, chunk_len, &mut ctr);
            (ciphertext, out_plaintext, len) = (
                ciphertext.add(chunk_len),
                out_plaintext.add(chunk_len),
                len - chunk_len,
            );
        } else {
            // this is a partial block; pad it with zeroes
            let mut ciphertext_block = Block::zero();
            ciphertext_block.overwrite_part_at(0, slice::from_raw_parts(ciphertext, len));
            auth.update_block(ciphertext_block);
            let mut plaintext_block = aes_key.encrypt_iv_xor_block(ctr.into(), ciphertext_block);
            plaintext_block.zero_from(len);
            ptr::copy_nonoverlapping(plaintext_block.as_ref()[..len].as_ptr(), out_plaintext, len);
            break;
        }
    }

    finish(aes_key, auth, tag_iv, aad_len, total_len)
}

fn finish(
    aes_key: &aes::Key,
    mut gcm_ctx: gcm::Context,
    tag_iv: aes::Iv,
    aad_len: usize,
    total_len: usize,
) -> Tag {
    // Authenticate the final block containing the input lengths.
    let aad_bits = polyfill::u64_from_usize(aad_len) << 3;
    let ciphertext_bits = polyfill::u64_from_usize(total_len) << 3;
    gcm_ctx.update_block(Block::from([aad_bits, ciphertext_bits]));

    // Finalize the tag and return it.
    gcm_ctx.pre_finish(|pre_tag| {
        let encrypted_iv = aes_key.encrypt_block(Block::from(tag_iv.as_bytes_less_safe()));
        let tag = pre_tag ^ encrypted_iv;
        Tag(*tag.as_ref())
    })
}

const AES_GCM_MAX_INPUT_LEN: u64 = super::max_input_len(BLOCK_LEN, 2);

#[cfg(test)]
mod tests {
    #[test]
    fn max_input_len_test() {
        // [NIST SP800-38D] Section 5.2.1.1. Note that [RFC 5116 Section 5.1] and
        // [RFC 5116 Section 5.2] have an off-by-one error in `P_MAX`.
        //
        // [NIST SP800-38D]:
        //    http://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
        // [RFC 5116 Section 5.1]: https://tools.ietf.org/html/rfc5116#section-5.1
        // [RFC 5116 Section 5.2]: https://tools.ietf.org/html/rfc5116#section-5.2
        const NIST_SP800_38D_MAX_BITS: u64 = (1u64 << 39) - 256;
        assert_eq!(NIST_SP800_38D_MAX_BITS, 549_755_813_632u64);
        assert_eq!(
            super::AES_128_GCM.max_input_len * 8,
            NIST_SP800_38D_MAX_BITS
        );
        assert_eq!(
            super::AES_256_GCM.max_input_len * 8,
            NIST_SP800_38D_MAX_BITS
        );
    }
}
