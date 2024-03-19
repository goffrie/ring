#![allow(clippy::cast_possible_truncation)]

#[cfg_attr(not(target_pointer_width = "64"), path = "soft/fixslice32.rs")]
#[cfg_attr(target_pointer_width = "64", path = "soft/fixslice64.rs")]
pub(crate) mod fixslice;

/// One AES block (128 bits)
pub(crate) type Block = [u8; 16];
