// Copyright 2018 Brian Smith.
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
    block::{Block, BLOCK_LEN},
    nonce::Nonce,
    quic::Sample,
};
use crate::{
    bits::{BitLength, FromUsizeBytes},
    c, cpu,
    endian::BigEndian,
    error,
    polyfill::{
        self,
        slice::{as_chunks, as_chunks_mut},
        ArraySplitMap,
    },
    rust_crypto::aes::soft::fixslice,
};
use core::ops::RangeFrom;

#[derive(Clone)]
pub(super) struct Key {
    inner: AesKey,
}

macro_rules! set_encrypt_key_asm {
    ( $name:ident, $bytes:expr, $key_bits:expr, $key:expr ) => {{
        prefixed_extern! {
            fn $name(user_key: *const u8, bits: c::uint, key: &mut AES_KEY) -> c::int;
        }
        set_encrypt_key_asm($name, $bytes, $key_bits, $key)
    }};
}

#[inline]
unsafe fn set_encrypt_key_asm(
    f: unsafe extern "C" fn(*const u8, c::uint, &mut AES_KEY) -> c::int,
    bytes: &[u8],
    key_bits: BitLength,
    key: &mut AES_KEY,
) -> Result<(), error::Unspecified> {
    // Unusually, in this case zero means success and non-zero means failure.
    #[allow(clippy::cast_possible_truncation)]
    if 0 == unsafe { f(bytes.as_ptr(), key_bits.as_bits() as c::uint, key) } {
        Ok(())
    } else {
        Err(error::Unspecified)
    }
}

macro_rules! encrypt_block_asm {
    ($name:ident, $block:expr, $key:expr) => {{
        prefixed_extern! {
            fn $name(a: &Block, r: *mut Block, key: &AES_KEY);
        }
        encrypt_block_($name, $block, $key)
    }};
}

#[inline]
unsafe fn encrypt_block_(
    f: unsafe extern "C" fn(&Block, *mut Block, &AES_KEY),
    a: Block,
    key: &Key,
) -> Block {
    let mut result = core::mem::MaybeUninit::uninit();
    unsafe {
        f(&a, result.as_mut_ptr(), key.inner.asm_key());
        result.assume_init()
    }
}

macro_rules! ctr32_encrypt_blocks_asm {
    ($name:ident, $in_out:expr, $src:expr, $key:expr, $ivec:expr ) => {{
        prefixed_extern! {
            fn $name(
                input: *const [u8; BLOCK_LEN],
                output: *mut [u8; BLOCK_LEN],
                blocks: c::size_t,
                key: &AES_KEY,
                ivec: &Counter,
            );
        }
        ctr32_encrypt_blocks_asm_($name, $in_out, $src, $key, $ivec)
    }};
}

#[inline]
unsafe fn ctr32_encrypt_blocks_asm_(
    f: unsafe extern "C" fn(
        input: *const [u8; BLOCK_LEN],
        output: *mut [u8; BLOCK_LEN],
        blocks: c::size_t,
        key: &AES_KEY,
        ivec: &Counter,
    ),
    in_out: &mut [u8],
    src: RangeFrom<usize>,
    key: &AES_KEY,
    ctr: &mut Counter,
) {
    let in_out_len = in_out[src.clone()].len();
    assert_eq!(in_out_len % BLOCK_LEN, 0);

    let blocks = in_out_len / BLOCK_LEN;
    #[allow(clippy::cast_possible_truncation)]
    let blocks_u32 = blocks as u32;
    assert_eq!(blocks, polyfill::usize_from_u32(blocks_u32));

    let input = in_out[src].as_ptr().cast::<[u8; BLOCK_LEN]>();
    let output = in_out.as_mut_ptr().cast::<[u8; BLOCK_LEN]>();

    unsafe {
        f(input, output, blocks, key, ctr);
    }
    ctr.increment_by_less_safe(blocks_u32);
}

fn xor_within(in_out: &mut [u8], src: RangeFrom<usize>, keystream: &[[u8; 16]]) {
    for (i, &keystream_block) in keystream.iter().enumerate() {
        let input_block = u128::from_ne_bytes(as_chunks(&in_out[src.clone()]).0[i]);
        let keystream_block = u128::from_ne_bytes(keystream_block);
        as_chunks_mut(in_out).0[i] = (input_block ^ keystream_block).to_ne_bytes();
    }
}

fn ctr32_encrypt_blocks_fixslice<K>(
    f: impl Fn(&K, &fixslice::BatchBlocks) -> fixslice::BatchBlocks,
    key: &K,
    in_out: &mut [u8],
    src: RangeFrom<usize>,
    ctr: &mut Counter,
) {
    let in_out_len = in_out[src.clone()].len();
    assert_eq!(in_out_len % BLOCK_LEN, 0);
    let blocks = in_out_len / BLOCK_LEN;
    let mut plaintext_batch = [[0; BLOCK_LEN]; fixslice::FIXSLICE_BLOCKS];
    let batches = blocks / fixslice::FIXSLICE_BLOCKS;
    for batch in 0..batches {
        for ctr_block in &mut plaintext_batch {
            *ctr_block = *ctr.increment().into_block_less_safe().as_ref();
        }
        let keystream_batch = f(key, &plaintext_batch);
        xor_within(
            &mut in_out[batch * fixslice::FIXSLICE_BLOCKS * BLOCK_LEN..],
            src.clone(),
            &keystream_batch,
        );
    }
    let leftover = blocks % fixslice::FIXSLICE_BLOCKS;
    if leftover > 0 {
        for ctr_block in &mut plaintext_batch[..leftover] {
            *ctr_block = *ctr.increment().into_block_less_safe().as_ref();
        }
        // plaintext_batch[leftover..] is just junk from previous iterations,
        // but we don't use it.
        let keystream_batch = f(key, &plaintext_batch);
        xor_within(
            &mut in_out[batches * fixslice::FIXSLICE_BLOCKS * BLOCK_LEN..],
            src.clone(),
            &keystream_batch[..leftover],
        );
    }
}

impl Key {
    #[inline]
    pub fn new(
        bytes: &[u8],
        variant: Variant,
        cpu_features: cpu::Features,
    ) -> Result<Self, error::Unspecified> {
        let key_bits = match variant {
            Variant::AES_128 => BitLength::from_usize_bits(128),
            Variant::AES_256 => BitLength::from_usize_bits(256),
        };
        if BitLength::from_usize_bytes(bytes.len())? != key_bits {
            return Err(error::Unspecified);
        }

        let key = match detect_implementation(cpu_features) {
            #[cfg(any(
                target_arch = "aarch64",
                target_arch = "arm",
                target_arch = "x86_64",
                target_arch = "x86"
            ))]
            Implementation::HWAES => {
                let mut key = AES_KEY::default();
                unsafe {
                    set_encrypt_key_asm!(aes_hw_set_encrypt_key, bytes, key_bits, &mut key)?;
                }
                AesKey::Asm(key)
            }

            #[cfg(any(
                target_arch = "aarch64",
                target_arch = "arm",
                target_arch = "x86_64",
                target_arch = "x86"
            ))]
            Implementation::VPAES_BSAES => {
                let mut key = AES_KEY::default();
                unsafe {
                    set_encrypt_key_asm!(vpaes_set_encrypt_key, bytes, key_bits, &mut key)?;
                }
                AesKey::Asm(key)
            }

            Implementation::NOHW => match variant {
                Variant::AES_128 => AesKey::Soft128(fixslice::aes128_key_schedule(
                    bytes.try_into().map_err(|_| error::Unspecified)?,
                )),
                Variant::AES_256 => AesKey::Soft256(fixslice::aes256_key_schedule(
                    bytes.try_into().map_err(|_| error::Unspecified)?,
                )),
            },
        };

        Ok(Self { inner: key })
    }

    #[inline]
    pub fn encrypt_block(&self, a: Block, cpu_features: cpu::Features) -> Block {
        match detect_implementation(cpu_features) {
            #[cfg(any(
                target_arch = "aarch64",
                target_arch = "arm",
                target_arch = "x86_64",
                target_arch = "x86"
            ))]
            Implementation::HWAES => unsafe { encrypt_block_asm!(aes_hw_encrypt, a, self) },

            #[cfg(any(
                target_arch = "aarch64",
                target_arch = "arm",
                target_arch = "x86_64",
                target_arch = "x86"
            ))]
            Implementation::VPAES_BSAES => unsafe { encrypt_block_asm!(vpaes_encrypt, a, self) },

            Implementation::NOHW => {
                let mut blocks = [[0; BLOCK_LEN]; fixslice::FIXSLICE_BLOCKS];
                blocks[0] = *a.as_ref();
                let ciphertext_blocks = match self.inner {
                    AesKey::Asm(_) => unreachable!(),
                    AesKey::Soft128(ref key) => fixslice::aes128_encrypt(key, &blocks),
                    AesKey::Soft256(ref key) => fixslice::aes256_encrypt(key, &blocks),
                };
                (&ciphertext_blocks[0]).into()
            }
        }
    }

    #[inline]
    pub fn encrypt_iv_xor_block(&self, iv: Iv, input: Block, cpu_features: cpu::Features) -> Block {
        let encrypted_iv = self.encrypt_block(iv.into_block_less_safe(), cpu_features);
        encrypted_iv ^ input
    }

    #[inline]
    pub(super) fn ctr32_encrypt_within(
        &self,
        in_out: &mut [u8],
        src: RangeFrom<usize>,
        ctr: &mut Counter,
        cpu_features: cpu::Features,
    ) {
        let in_out_len = in_out[src.clone()].len();

        assert_eq!(in_out_len % BLOCK_LEN, 0);

        match detect_implementation(cpu_features) {
            #[cfg(any(
                target_arch = "aarch64",
                target_arch = "arm",
                target_arch = "x86_64",
                target_arch = "x86"
            ))]
            Implementation::HWAES => unsafe {
                ctr32_encrypt_blocks_asm!(
                    aes_hw_ctr32_encrypt_blocks,
                    in_out,
                    src,
                    self.inner.asm_key(),
                    ctr
                )
            },

            #[cfg(any(target_arch = "aarch64", target_arch = "arm", target_arch = "x86_64"))]
            Implementation::VPAES_BSAES => {
                // 8 blocks is the cut-off point where it's faster to use BSAES.
                #[cfg(target_arch = "arm")]
                let in_out = if in_out_len >= 8 * BLOCK_LEN {
                    let remainder = in_out_len % (8 * BLOCK_LEN);
                    let bsaes_in_out_len = if remainder < (4 * BLOCK_LEN) {
                        in_out_len - remainder
                    } else {
                        in_out_len
                    };

                    let mut bsaes_key = AES_KEY {
                        rd_key: [0u32; 4 * (MAX_ROUNDS + 1)],
                        rounds: 0,
                    };
                    prefixed_extern! {
                        fn vpaes_encrypt_key_to_bsaes(bsaes_key: &mut AES_KEY, vpaes_key: &AES_KEY);
                    }
                    unsafe {
                        vpaes_encrypt_key_to_bsaes(&mut bsaes_key, self.inner.asm_key());
                        ctr32_encrypt_blocks_asm!(
                            bsaes_ctr32_encrypt_blocks,
                            &mut in_out[..(src.start + bsaes_in_out_len)],
                            src.clone(),
                            &bsaes_key,
                            ctr
                        );
                    }

                    &mut in_out[bsaes_in_out_len..]
                } else {
                    in_out
                };

                unsafe {
                    ctr32_encrypt_blocks_asm!(
                        vpaes_ctr32_encrypt_blocks,
                        in_out,
                        src,
                        self.inner.asm_key(),
                        ctr
                    )
                }
            }

            #[cfg(target_arch = "x86")]
            Implementation::VPAES_BSAES => {
                super::shift::shift_full_blocks(in_out, src, |input| {
                    self.encrypt_iv_xor_block(ctr.increment(), Block::from(input), cpu_features)
                });
            }

            Implementation::NOHW => match self.inner {
                AesKey::Asm(_) => unreachable!(),
                AesKey::Soft128(ref key) => {
                    ctr32_encrypt_blocks_fixslice(fixslice::aes128_encrypt, key, in_out, src, ctr)
                }
                AesKey::Soft256(ref key) => {
                    ctr32_encrypt_blocks_fixslice(fixslice::aes256_encrypt, key, in_out, src, ctr)
                }
            },
        }
    }

    pub fn new_mask(&self, sample: Sample) -> [u8; 5] {
        let block = self.encrypt_block(Block::from(&sample), cpu::features());

        let mut out: [u8; 5] = [0; 5];
        out.copy_from_slice(&block.as_ref()[..5]);

        out
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    #[must_use]
    pub fn is_aes_hw(&self, cpu_features: cpu::Features) -> bool {
        matches!(detect_implementation(cpu_features), Implementation::HWAES)
    }

    /// # Safety
    /// Requires that `self.is_aes_hw()` is `true`.
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    #[must_use]
    pub(super) unsafe fn inner_less_safe(&self) -> &AES_KEY {
        self.inner.asm_key()
    }
}

// AES_KEY structure used by assembly language aes_hw routines.
#[repr(C)]
#[derive(Copy, Clone)]
pub(crate) struct AES_KEY {
    pub rd_key: [u32; 4 * (MAX_ROUNDS + 1)],
    pub rounds: c::uint,
}

impl Default for AES_KEY {
    fn default() -> Self {
        Self {
            rd_key: [0; 4 * (MAX_ROUNDS + 1)],
            rounds: 0,
        }
    }
}

// Maximum number of rounds for AES; AES-256 has 14 rounds.
const MAX_ROUNDS: usize = 14;

#[allow(clippy::large_enum_variant)]
#[derive(Copy, Clone)]
enum AesKey {
    Asm(AES_KEY),
    Soft128(fixslice::FixsliceKeys128),
    Soft256(fixslice::FixsliceKeys256),
}

impl AesKey {
    fn asm_key(&self) -> &AES_KEY {
        match self {
            AesKey::Asm(key) => key,
            _ => unreachable!(),
        }
    }
}

pub enum Variant {
    AES_128,
    AES_256,
}

/// Nonce || Counter, all big-endian.
#[repr(transparent)]
pub(super) struct Counter([BigEndian<u32>; 4]);

impl Counter {
    pub fn one(nonce: Nonce) -> Self {
        let [n0, n1, n2] = nonce.as_ref().array_split_map(BigEndian::<u32>::from);
        Self([n0, n1, n2, 1.into()])
    }

    pub fn increment(&mut self) -> Iv {
        let iv: [[u8; 4]; 4] = self.0.map(Into::into);
        let iv = Iv(Block::from(iv));
        self.increment_by_less_safe(1);
        iv
    }

    fn increment_by_less_safe(&mut self, increment_by: u32) {
        let old_value: u32 = self.0[3].into();
        self.0[3] = (old_value + increment_by).into();
    }
}

/// The IV for a single block encryption.
///
/// Intentionally not `Clone` to ensure each is used only once.
pub struct Iv(Block);

impl From<Counter> for Iv {
    fn from(counter: Counter) -> Self {
        let iv: [[u8; 4]; 4] = counter.0.map(Into::into);
        Self(Block::from(iv))
    }
}

impl Iv {
    /// "Less safe" because it defeats attempts to use the type system to prevent reuse of the IV.
    #[inline]
    pub(super) fn into_block_less_safe(self) -> Block {
        self.0
    }
}

#[repr(C)] // Only so `Key` can be `#[repr(C)]`
#[derive(Clone, Copy)]
#[allow(clippy::upper_case_acronyms)]
pub enum Implementation {
    #[cfg(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86_64",
        target_arch = "x86"
    ))]
    HWAES = 1,

    // On "arm" only, this indicates that the bsaes implementation may be used.
    #[cfg(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86_64",
        target_arch = "x86"
    ))]
    VPAES_BSAES = 2,

    NOHW = 3,
}

fn detect_implementation(cpu_features: cpu::Features) -> Implementation {
    // `cpu_features` is only used for specific platforms.
    #[cfg(not(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86_64",
        target_arch = "x86"
    )))]
    let _cpu_features = cpu_features;

    #[cfg(any(target_arch = "aarch64", target_arch = "arm"))]
    {
        if cpu::arm::AES.available(cpu_features) {
            return Implementation::HWAES;
        }
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    {
        if cpu::intel::AES.available(cpu_features) {
            return Implementation::HWAES;
        }
    }

    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    {
        if cpu::intel::SSSE3.available(cpu_features) {
            return Implementation::VPAES_BSAES;
        }
    }

    #[cfg(any(target_arch = "aarch64", target_arch = "arm"))]
    {
        if cpu::arm::NEON.available(cpu_features) {
            return Implementation::VPAES_BSAES;
        }
    }

    {
        Implementation::NOHW
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test;

    #[test]
    pub fn test_aes() {
        let cpu_features = cpu::features();
        test::run(test_file!("aes_tests.txt"), |section, test_case| {
            assert_eq!(section, "");
            let key = consume_key(test_case, "Key");
            let input = test_case.consume_bytes("Input");
            let input: &[u8; BLOCK_LEN] = input.as_slice().try_into()?;
            let expected_output = test_case.consume_bytes("Output");

            let block = Block::from(input);
            let output = key.encrypt_block(block, cpu_features);
            assert_eq!(output.as_ref(), &expected_output[..]);

            Ok(())
        })
    }

    fn consume_key(test_case: &mut test::TestCase, name: &str) -> Key {
        let key = test_case.consume_bytes(name);
        let variant = match key.len() {
            16 => Variant::AES_128,
            32 => Variant::AES_256,
            _ => unreachable!(),
        };
        Key::new(&key[..], variant, cpu::features()).unwrap()
    }
}
