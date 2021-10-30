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

use crate::{Bech32Scheme, BlockError};
use snarkvm_fields::{ConstraintFieldError, Field, ToConstraintField};
use snarkvm_utilities::{
    fmt,
    io::{Read, Result as IoResult, Write},
    ops::Deref,
    str,
    str::FromStr,
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
};

use anyhow::Result;
use bech32::{self, FromBase32, ToBase32};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    borrow::Borrow,
    hash::{Hash, Hasher},
};

#[derive(Copy, Clone, Default, PartialEq, Eq)]
pub struct Bech32<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize>(F);

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> Bech32Scheme<F>
    for Bech32<F, PREFIX, DATA_SIZE>
{
    #[inline]
    fn new(data: F) -> Self {
        Self(data)
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> From<F>
    for Bech32<F, PREFIX, DATA_SIZE>
{
    #[inline]
    fn from(data: F) -> Self {
        Self(data)
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> FromBytes
    for Bech32<F, PREFIX, DATA_SIZE>
{
    /// Reads data into a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self(FromBytes::read_le(&mut reader)?))
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> ToBytes
    for Bech32<F, PREFIX, DATA_SIZE>
{
    /// Writes the data to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> FromStr
    for Bech32<F, PREFIX, DATA_SIZE>
{
    type Err = BlockError;

    /// Reads in a bech32 string.
    #[inline]
    fn from_str(string: &str) -> Result<Self, Self::Err> {
        if string.len() != 61 {
            return Err(BlockError::InvalidCharacterLength(string.len()));
        }

        let (hrp, data, _variant) = bech32::decode(&string)?;
        if hrp.as_bytes() != &PREFIX.to_le_bytes() {
            return Err(BlockError::InvalidPrefix(string.to_lowercase()[0..2].to_string()));
        };
        if data.is_empty() {
            return Err(BlockError::InvalidByteLength(0));
        }

        let buffer = Vec::from_base32(&data)?;
        Ok(Self::read_le(&buffer[..])?)
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> fmt::Display
    for Bech32<F, PREFIX, DATA_SIZE>
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        bech32::encode(
            str::from_utf8(&PREFIX.to_le_bytes()).expect("Failed to convert prefix to string"),
            self.0.to_bytes_le().expect("Failed to write data as bytes").to_base32(),
            bech32::Variant::Bech32,
        )
        .expect("Failed to encode in bech32")
        .fmt(f)
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> fmt::Debug
    for Bech32<F, PREFIX, DATA_SIZE>
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Bech32 {{ hrp: {:?}, data: {:?} }}", PREFIX, self.0)
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> Serialize
    for Bech32<F, PREFIX, DATA_SIZE>
{
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> Deserialize<'de>
    for Bech32<F, PREFIX, DATA_SIZE>
{
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize(
                deserializer,
                str::from_utf8(&PREFIX.to_le_bytes()).expect("Failed to convert prefix to string"),
                DATA_SIZE,
            ),
        }
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> ToConstraintField<F>
    for Bech32<F, PREFIX, DATA_SIZE>
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        self.0.to_field_elements()
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> Hash for Bech32<F, PREFIX, DATA_SIZE> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> Deref
    for Bech32<F, PREFIX, DATA_SIZE>
{
    type Target = F;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F: Field + ToConstraintField<F>, const PREFIX: u16, const DATA_SIZE: usize> Borrow<F>
    for Bech32<F, PREFIX, DATA_SIZE>
{
    #[inline]
    fn borrow(&self) -> &F {
        &self.0
    }
}
