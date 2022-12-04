// Copyright 2015-2021 Brian Smith.
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

use super::{Aad, Algorithm, KeyInner, Nonce, Tag, UnboundKey, TAG_LEN};
use crate::{constant_time, cpu, error, polyfill};
use core::ops::RangeFrom;

/// Immutable keys for use in situations where `OpeningKey`/`SealingKey` and
/// `NonceSequence` cannot reasonably be used.
///
/// Prefer to use `OpeningKey`/`SealingKey` and `NonceSequence` when practical.
#[derive(Clone)]
pub struct LessSafeKey {
    inner: KeyInner,
    algorithm: &'static Algorithm,
}

impl LessSafeKey {
    /// Constructs a `LessSafeKey`.
    #[inline]
    pub fn new(key: UnboundKey) -> Self {
        key.into_inner()
    }

    pub(super) fn new_(
        algorithm: &'static Algorithm,
        key_bytes: &[u8],
    ) -> Result<Self, error::Unspecified> {
        let cpu_features = cpu::features();
        Ok(Self {
            inner: (algorithm.init)(key_bytes, cpu_features)?,
            algorithm,
        })
    }

    /// Like [open_in_place](Self::open_in_place), except the authentication tag is
    /// passed separately.
    #[inline]
    pub fn open_in_place_separate_tag<'in_out, A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        tag: Tag,
        in_out: &'in_out mut [u8],
        ciphertext: RangeFrom<usize>,
    ) -> Result<&'in_out mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let aad = Aad::from(aad.as_ref());
        open_within_(self, nonce, aad, tag, in_out, ciphertext)
    }

    /// Like [`super::OpeningKey::open_in_place()`], except it accepts an
    /// arbitrary nonce.
    ///
    /// `nonce` must be unique for every use of the key to open data.
    #[inline]
    pub fn open_in_place<'in_out, A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &'in_out mut [u8],
    ) -> Result<&'in_out mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        self.open_within(nonce, aad, in_out, 0..)
    }

    /// Like [`super::OpeningKey::open_within()`], except it accepts an
    /// arbitrary nonce.
    ///
    /// `nonce` must be unique for every use of the key to open data.
    #[inline]
    pub fn open_within<'in_out, A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &'in_out mut [u8],
        ciphertext_and_tag: RangeFrom<usize>,
    ) -> Result<&'in_out mut [u8], error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let tag_offset = in_out
            .len()
            .checked_sub(TAG_LEN)
            .ok_or(error::Unspecified)?;

        // Split the tag off the end of `in_out`.
        let (in_out, received_tag) = in_out.split_at_mut(tag_offset);
        let received_tag = (*received_tag).try_into()?;
        let ciphertext = ciphertext_and_tag;

        self.open_in_place_separate_tag(nonce, aad, received_tag, in_out, ciphertext)
    }

    /// Like [`super::OpeningKey::open_to_vec()`], except it accepts an
    /// arbitrary nonce.
    ///
    /// `nonce` must be unique for every use of the key to open data.
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn open_to_vec<A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        ciphertext_and_tag: &[u8],
        output: &mut alloc::vec::Vec<u8>,
    ) -> Result<(), error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let ciphertext_len = ciphertext_and_tag
            .len()
            .checked_sub(TAG_LEN)
            .ok_or(error::Unspecified)?;
        check_per_nonce_max_bytes(self.algorithm, ciphertext_len)?;
        let received_tag = Tag(ciphertext_and_tag[ciphertext_len..].try_into()?);
        let aad = Aad::from(aad.as_ref());
        let ciphertext = &ciphertext_and_tag[..ciphertext_len];
        output.reserve(ciphertext_len);
        unsafe {
            // Safety: `ciphertext` is a slice with length `ciphertext_len`, so `ciphertext.as_ptr()` points to `ciphertext_len` readable bytes.
            // `out` has additional capacity at least `ciphertext_len`, so `output.spare_capacity_mut()` points to `ciphertext_len` writable bytes.
            let calculated_tag = (self.algorithm.open)(
                &self.inner,
                nonce,
                aad,
                ciphertext.as_ptr(),
                output.spare_capacity_mut().as_mut_ptr().cast::<u8>(),
                ciphertext_len,
            );
            constant_time::verify_slices_are_equal(calculated_tag.as_ref(), received_tag.as_ref())?;
            // We wait until the tag is verified before extending `output`.
            // XXX: is this safe enough? the unchecked plaintext is technically still accessible
            // Safety: `self.algorithm.open` promises to initialize the first `ciphertext_len` bytes of its output pointer.
            output.set_len(output.len() + ciphertext_len);
        }
        Ok(())
    }

    /// Like [`super::SealingKey::seal_in_place_append_tag()`], except it
    /// accepts an arbitrary nonce.
    ///
    /// `nonce` must be unique for every use of the key to seal data.
    #[inline]
    pub fn seal_in_place_append_tag<A, InOut>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &mut InOut,
    ) -> Result<(), error::Unspecified>
    where
        A: AsRef<[u8]>,
        InOut: AsMut<[u8]> + for<'in_out> Extend<&'in_out u8>,
    {
        self.seal_in_place_separate_tag(nonce, aad, in_out.as_mut())
            .map(|tag| in_out.extend(tag.as_ref()))
    }

    /// Like `super::SealingKey::seal_in_place_separate_tag()`, except it
    /// accepts an arbitrary nonce.
    ///
    /// `nonce` must be unique for every use of the key to seal data.
    #[inline]
    pub fn seal_in_place_separate_tag<A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &mut [u8],
    ) -> Result<Tag, error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        seal_in_place_separate_tag_(self, nonce, Aad::from(aad.as_ref()), in_out)
    }

    /// Like [`super::SealingKey::seal_to_vec_separate_tag()`], except it accepts an
    /// arbitrary nonce.
    ///
    /// `nonce` must be unique for every use of the key to open data.
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn seal_to_vec_separate_tag<A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        plaintext: &[u8],
        output: &mut alloc::vec::Vec<u8>,
    ) -> Result<Tag, error::Unspecified>
    where
        A: AsRef<[u8]>,
    {
        let plaintext_len = plaintext.len();
        check_per_nonce_max_bytes(self.algorithm, plaintext_len)?;
        let aad = Aad::from(aad.as_ref());
        output.reserve(plaintext_len);
        unsafe {
            // Safety: `plaintext` is a slice with length `plaintext_len`, so `plaintext.as_ptr()` points to `plaintext_len` readable bytes.
            // `output` has additional capacity at least `plaintext_len`, so `output.spare_capacity_mut()` points to `plaintext_len` writable bytes.
            let tag = (self.algorithm.seal)(
                &self.inner,
                nonce,
                aad,
                plaintext.as_ptr(),
                output.spare_capacity_mut().as_mut_ptr().cast::<u8>(),
                plaintext_len,
            );
            // Safety: `self.algorithm.seal` promises to initialize the first `plaintext_len` bytes of its output pointer.
            output.set_len(output.len() + plaintext_len);
            Ok(tag)
        }
    }

    /// The key's AEAD algorithm.
    #[inline]
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    pub(super) fn fmt_debug(
        &self,
        type_name: &'static str,
        f: &mut core::fmt::Formatter,
    ) -> Result<(), core::fmt::Error> {
        f.debug_struct(type_name)
            .field("algorithm", &self.algorithm())
            .finish()
    }
}

fn open_within_<'in_out>(
    key: &LessSafeKey,
    nonce: Nonce,
    aad: Aad<&[u8]>,
    received_tag: Tag,
    in_out: &'in_out mut [u8],
    src: RangeFrom<usize>,
) -> Result<&'in_out mut [u8], error::Unspecified> {
    let ciphertext_len = in_out
        .len()
        .checked_sub(src.start)
        .ok_or(error::Unspecified)?;
    check_per_nonce_max_bytes(key.algorithm, ciphertext_len)?;

    let Tag(calculated_tag) = unsafe {
        let in_out_ptr = in_out.as_mut_ptr();
        // Safety: `in_out_ptr` points to `in_out.len()` valid read/writeable bytes.
        // Therefore `in_out_ptr.add(src.start)` is valid for `in_out.len() - src.start` bytes;
        // that is equal to `ciphertext_len`.
        (key.algorithm.open)(
            &key.inner,
            nonce,
            aad,
            in_out_ptr.add(src.start),
            in_out_ptr,
            ciphertext_len,
        )
    };

    if constant_time::verify_slices_are_equal(calculated_tag.as_ref(), received_tag.as_ref())
        .is_err()
    {
        // Zero out the plaintext so that it isn't accidentally leaked or used
        // after verification fails. It would be safest if we could check the
        // tag before decrypting, but some `open` implementations interleave
        // authentication with decryption for performance.
        for b in &mut in_out[..ciphertext_len] {
            *b = 0;
        }
        return Err(error::Unspecified);
    }

    // `ciphertext_len` is also the plaintext length.
    Ok(&mut in_out[..ciphertext_len])
}

#[inline]
pub(super) fn seal_in_place_separate_tag_(
    key: &LessSafeKey,
    nonce: Nonce,
    aad: Aad<&[u8]>,
    in_out: &mut [u8],
) -> Result<Tag, error::Unspecified> {
    check_per_nonce_max_bytes(key.algorithm(), in_out.len())?;
    Ok(unsafe {
        let in_out_ptr = in_out.as_mut_ptr();
        // Safety: `in_out_ptr` points to `in_out.len()` valid read/writeable bytes.
        (key.algorithm.seal)(&key.inner, nonce, aad, in_out_ptr, in_out_ptr, in_out.len())
    })
}

fn check_per_nonce_max_bytes(alg: &Algorithm, in_out_len: usize) -> Result<(), error::Unspecified> {
    if polyfill::u64_from_usize(in_out_len) > alg.max_input_len {
        return Err(error::Unspecified);
    }
    Ok(())
}

impl core::fmt::Debug for LessSafeKey {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        self.fmt_debug("LessSafeKey", f)
    }
}
