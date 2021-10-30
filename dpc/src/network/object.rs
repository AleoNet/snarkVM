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

use crate::{Bech32Object, Bech32Prefix, Bech32mError};
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
use snarkvm_utilities::marker::PhantomData;
use std::{borrow::Borrow, fmt::Debug, hash::Hash};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AleoObject<
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
>(T, PhantomData<P>);

impl<
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> Bech32Object<P, T> for AleoObject<P, T, DATA_SIZE_IN_BYTES>
{
    #[inline]
    fn prefix() -> String {
        P::PREFIX.to_string()
    }

    #[inline]
    fn prefix_length() -> usize {
        P::PREFIX.len()
    }
}

impl<
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> From<T> for AleoObject<P, T, DATA_SIZE_IN_BYTES>
{
    #[inline]
    fn from(data: T) -> Self {
        Self(data, PhantomData)
    }
}

impl<
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> FromBytes for AleoObject<P, T, DATA_SIZE_IN_BYTES>
{
    /// Reads data into a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self(FromBytes::read_le(&mut reader)?, PhantomData))
    }
}

impl<
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> ToBytes for AleoObject<P, T, DATA_SIZE_IN_BYTES>
{
    /// Writes the data to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> FromStr for AleoObject<P, T, DATA_SIZE_IN_BYTES>
{
    type Err = Bech32mError;

    /// Reads in a bech32m string.
    #[inline]
    fn from_str(string: &str) -> Result<Self, Self::Err> {
        let (hrp, data, variant) = bech32::decode(&string)?;
        if hrp != Self::prefix() {
            return Err(Bech32mError::InvalidPrefix(hrp));
        };
        if data.is_empty() {
            return Err(Bech32mError::InvalidByteLength(0));
        }
        if variant != bech32::Variant::Bech32m {
            return Err(Bech32mError::InvalidVariant);
        }

        let buffer = Vec::from_base32(&data)?;
        Ok(Self::read_le(&buffer[..])?)
    }
}

impl<
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> fmt::Display for AleoObject<P, T, DATA_SIZE_IN_BYTES>
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> Debug for AleoObject<P, T, DATA_SIZE_IN_BYTES>
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "AleoObject {{ hrp: {:?}, data: {:?} }}", &Self::prefix(), self.0)
    }
}

impl<
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> Serialize for AleoObject<P, T, DATA_SIZE_IN_BYTES>
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
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> Deserialize<'de> for AleoObject<P, T, DATA_SIZE_IN_BYTES>
{
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize(deserializer, &Self::prefix(), DATA_SIZE_IN_BYTES),
        }
    }
}

impl<
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> Deref for AleoObject<P, T, DATA_SIZE_IN_BYTES>
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<
    P: Bech32Prefix,
    T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send,
    const DATA_SIZE_IN_BYTES: usize,
> Borrow<T> for AleoObject<P, T, DATA_SIZE_IN_BYTES>
{
    #[inline]
    fn borrow(&self) -> &T {
        &self.0
    }
}
