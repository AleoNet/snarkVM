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
use snarkvm_fields::{ConstraintFieldError, PrimeField, ToConstraintField};
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
    UniformRand,
};

use anyhow::Result;
use bech32::{self, FromBase32, ToBase32};
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::borrow::Borrow;

#[derive(Copy, Clone, Default, PartialEq, Eq, Hash)]
pub struct Bech32<F: PrimeField + ToConstraintField<F>, const PREFIX: u16>(F);

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> Bech32Scheme<F> for Bech32<F, PREFIX> {
    #[inline]
    fn prefix() -> String {
        String::from_utf8(PREFIX.to_le_bytes().to_vec()).expect("Failed to convert prefix to string")
    }

    #[inline]
    fn data_size_in_bytes() -> usize {
        (F::size_in_bits() + 7) / 8
    }

    #[inline]
    fn data_string_length() -> usize {
        ((Self::data_size_in_bytes() * 8) + 4) / 5
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> From<F> for Bech32<F, PREFIX> {
    #[inline]
    fn from(data: F) -> Self {
        Self(data)
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> FromBytes for Bech32<F, PREFIX> {
    /// Reads data into a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self(FromBytes::read_le(&mut reader)?))
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> ToBytes for Bech32<F, PREFIX> {
    /// Writes the data to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> FromStr for Bech32<F, PREFIX> {
    type Err = BlockError;

    /// Reads in a bech32 string.
    #[inline]
    fn from_str(string: &str) -> Result<Self, Self::Err> {
        const CHECKSUM_STRING_LENGTH: usize = 6;
        if string.len() != 3 + Self::data_string_length() + CHECKSUM_STRING_LENGTH {
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

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> fmt::Display for Bech32<F, PREFIX> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        bech32::encode_to_fmt(
            f,
            &Self::prefix(),
            self.0.to_bytes_le().expect("Failed to write data as bytes").to_base32(),
            bech32::Variant::Bech32,
        )
        .expect("Failed to encode in bech32")
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> fmt::Debug for Bech32<F, PREFIX> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Bech32 {{ hrp: {:?}, data: {:?} }}", &Self::prefix(), self.0)
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> Serialize for Bech32<F, PREFIX> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, F: PrimeField + ToConstraintField<F>, const PREFIX: u16> Deserialize<'de> for Bech32<F, PREFIX> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => {
                FromBytesDeserializer::<Self>::deserialize(deserializer, &Self::prefix(), Self::data_size_in_bytes())
            }
        }
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> ToConstraintField<F> for Bech32<F, PREFIX> {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        self.0.to_field_elements()
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> Deref for Bech32<F, PREFIX> {
    type Target = F;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> Borrow<F> for Bech32<F, PREFIX> {
    #[inline]
    fn borrow(&self) -> &F {
        &self.0
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> Into<Vec<F>> for Bech32<F, PREFIX> {
    #[inline]
    fn into(self) -> Vec<F> {
        vec![self.0]
    }
}

impl<F: PrimeField + ToConstraintField<F>, const PREFIX: u16> Distribution<Bech32<F, PREFIX>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Bech32<F, PREFIX> {
        Bech32::<F, PREFIX>(UniformRand::rand(rng))
    }
}
