// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use crate::SerializationError;
pub use crate::{
    io::{
        Read,
        Write,
        {self},
    },
    FromBytes,
    ToBytes,
    Vec,
};

/// Serialization flags.
pub trait Flags: Default + Clone + Copy + Sized {
    /// Returns a bit mask corresponding to `self`.
    ///
    /// For example, if `Self` contains two variants, then there are two possible bit masks:
    /// `0` and `1 << 7`.
    fn u8_bitmask(&self) -> u8;

    /// Reads `Self` from `value`.
    fn from_u8(value: u8) -> Self;

    /// Convenience method that reads `Self` from `value`, just like `Self::from_u8`,
    /// but additionally zeroes out the bits corresponding to the resulting flag in `value`.
    fn from_u8_remove_flags(value: &mut u8) -> Self {
        let flags = Self::from_u8(*value);
        *value &= !flags.u8_bitmask();
        flags
    }

    /// Number of bits required for these flags.
    fn num_bits() -> usize;
}

/// Serializer in little endian format.
/// This trait can be derived if all fields of a struct implement
/// `CanonicalSerialize` and the `derive` feature is enabled.
///
/// # Example
/// ```
/// // The `derive` feature must be set for the derivation to work.
/// use snarkvm_utilities::serialize::*;
/// use snarkvm_utilities::errors::SerializationError;
///
/// # #[cfg(feature = "derive")]
/// #[derive(CanonicalSerialize)]
/// struct TestStruct {
///     a: u64,
///     b: (u64, (u64, u64)),
/// }
/// ```
pub trait CanonicalSerialize {
    /// Serializes `self` into `writer`.
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError>;

    fn serialized_size(&self) -> usize;

    /// Serializes `self` into `writer` without compression.
    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.serialize(writer)
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        self.serialized_size()
    }
}

/// Serializer in little endian format allowing to encode flags.
pub trait CanonicalSerializeWithFlags: CanonicalSerialize {
    /// Serializes `self` and `flags` into `writer`.
    fn serialize_with_flags<W: Write, F: Flags>(&self, writer: &mut W, flags: F) -> Result<(), SerializationError>;
}

/// Helper trait to get serialized size for constant sized structs.
pub trait ConstantSerializedSize: CanonicalSerialize {
    const SERIALIZED_SIZE: usize;
    const UNCOMPRESSED_SIZE: usize;
}

/// Deserializer in little endian format.
/// This trait can be derived if all fields of a struct implement
/// `CanonicalDeserialize` and the `derive` feature is enabled.
///
/// # Example
/// ```
/// // The `derive` feature must be set for the derivation to work.
/// use snarkvm_utilities::serialize::*;
/// use snarkvm_utilities::errors::SerializationError;
///
/// # #[cfg(feature = "derive")]
/// #[derive(CanonicalDeserialize)]
/// struct TestStruct {
///     a: u64,
///     b: (u64, (u64, u64)),
/// }
/// ```
pub trait CanonicalDeserialize: Sized {
    /// Reads `Self` from `reader`.
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError>;

    /// Reads `Self` from `reader` without compression.
    #[inline]
    fn deserialize_uncompressed<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        Self::deserialize(reader)
    }
}

/// Deserializer in little endian format allowing flags to be encoded.
pub trait CanonicalDeserializeWithFlags: Sized {
    /// Reads `Self` and `Flags` from `reader`.
    /// Returns empty flags by default.
    fn deserialize_with_flags<R: Read, F: Flags>(reader: &mut R) -> Result<(Self, F), SerializationError>;
}
