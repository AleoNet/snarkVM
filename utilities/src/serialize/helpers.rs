// Copyright (C) 2019-2023 Aleo Systems Inc.
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

pub use crate::{
    io::{self, Read, Write},
    FromBytes,
    ToBytes,
    Vec,
};
use crate::{serialize::traits::*, SerializationError};

/// Serialize a Vector's elements without serializing the Vector's length
/// If you want to serialize the full Vector, use `CanonicalSerialize for Vec<T>`
pub fn serialize_vec_without_len<'a>(
    src: impl Iterator<Item = &'a (impl CanonicalSerialize + 'a)>,
    mut writer: impl Write,
    compress: Compress,
) -> Result<(), SerializationError> {
    for elem in src {
        CanonicalSerialize::serialize_with_mode(elem, &mut writer, compress)?;
    }
    Ok(())
}

/// Serialize a Vector's element sizes without serializing the Vector's length
/// If you want to serialize the full Vector, use `CanonicalSerialize for Vec<T>`
pub fn serialized_vec_size_without_len(src: &[impl CanonicalSerialize], compress: Compress) -> usize {
    if src.is_empty() { 0 } else { src.len() * CanonicalSerialize::serialized_size(&src[0], compress) }
}

/// Deserialize a Vector's elements without deserializing the Vector's length
/// If you want to deserialize the full Vector, use `CanonicalDeserialize for Vec<T>`
pub fn deserialize_vec_without_len<T: CanonicalDeserialize>(
    mut reader: impl Read,
    compress: Compress,
    validate: Validate,
    len: usize,
) -> Result<Vec<T>, SerializationError> {
    (0..len).map(|_| CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)).collect()
}
