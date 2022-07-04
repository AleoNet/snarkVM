// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::prelude::*;

use anyhow::Result;
use bech32::{self, FromBase32, ToBase32};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::borrow::Borrow;

pub trait Bech32Object<T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send>:
    From<T>
    + Borrow<T>
    + Deref<Target = T>
    + Clone
    + Debug
    + Display
    + ToBytes
    + FromBytes
    + PartialEq
    + Eq
    + Serialize
    + DeserializeOwned
    + Sync
    + Send
{
    fn prefix() -> String;
    fn size_in_bytes() -> usize;
}

/// Converts a string of 4 characters into a `u32` for a human-readable prefix in Bech32.
#[macro_export]
macro_rules! hrp4 {
    ( $persona: expr ) => {{
        $crate::const_assert!($persona.len() == 4);
        let p = $persona.as_bytes();
        u32::from_le_bytes([p[0], p[1], p[2], p[3]])
    }};
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AleoObject<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
>(T);

impl<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> Bech32Object<T> for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    #[inline]
    fn prefix() -> String {
        String::from_utf8(PREFIX.to_le_bytes().to_vec()).expect("Failed to convert prefix to string")
    }

    #[inline]
    fn size_in_bytes() -> usize {
        SIZE_IN_DATA_BYTES
    }
}

impl<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> From<T> for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    #[inline]
    fn from(data: T) -> Self {
        Self(data)
    }
}

impl<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> FromBytes for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    /// Reads data into a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self(FromBytes::read_le(&mut reader)?))
    }
}

impl<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> ToBytes for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    /// Writes the data to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> FromStr for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    type Err = Error;

    /// Reads in a bech32m string.
    #[inline]
    fn from_str(string: &str) -> Result<Self, Self::Err> {
        let (hrp, data, variant) = bech32::decode(string)?;
        if hrp.as_bytes() != PREFIX.to_le_bytes() {
            bail!("Invalid prefix for a bech32m hash: {hrp}")
        };
        if data.is_empty() {
            bail!("Bech32m hash data is empty")
        }
        if variant != bech32::Variant::Bech32m {
            bail!("Hash is not a bech32m hash")
        }
        Ok(Self::read_le(&*Vec::from_base32(&data)?)?)
    }
}

impl<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> Display for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        bech32::encode_to_fmt(
            f,
            &Self::prefix(),
            self.0.to_bytes_le().expect("Failed to write data as bytes").to_base32(),
            bech32::Variant::Bech32m,
        )
        .expect("Failed to encode in bech32m")
    }
}

impl<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> Debug for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "AleoObject {{ hrp: {:?}, data: {:?} }}", &Self::prefix(), self.0)
    }
}

impl<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> Serialize for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<
    'de,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> Deserialize<'de> for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize(deserializer, &Self::prefix(), SIZE_IN_DATA_BYTES),
        }
    }
}

impl<
    T: Default + Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> Default for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    fn default() -> Self {
        Self(T::default())
    }
}

impl<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> Deref for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send,
    const PREFIX: u32,
    const SIZE_IN_DATA_BYTES: usize,
> Borrow<T> for AleoObject<T, PREFIX, SIZE_IN_DATA_BYTES>
{
    #[inline]
    fn borrow(&self) -> &T {
        &self.0
    }
}
