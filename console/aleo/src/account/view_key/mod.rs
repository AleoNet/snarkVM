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

use crate::{ComputeKey, Network, PrivateKey};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
};

use anyhow::{anyhow, bail, Error};
use base58::{FromBase58, ToBase58};
use core::{fmt, ops::Deref, str::FromStr};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

pub static VIEW_KEY_PREFIX: [u8; 7] = [14, 138, 223, 204, 247, 224, 122]; // AViewKey1

/// The account view key used to decrypt records and ciphertext.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ViewKey<N: Network>(N::Scalar);

impl<N: Network> TryFrom<PrivateKey<N>> for ViewKey<N> {
    type Error = Error;

    /// Initializes a new account view key from an account private key.
    fn try_from(private_key: PrivateKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&private_key)
    }
}

impl<N: Network> TryFrom<&PrivateKey<N>> for ViewKey<N> {
    type Error = Error;

    /// Initializes a new account view key from an account private key.
    fn try_from(private_key: &PrivateKey<N>) -> Result<Self, Self::Error> {
        // Derive the compute key.
        let compute_key = ComputeKey::try_from(private_key)?;
        // Compute view_key := sk_sig + r_sig + sk_prf.
        Ok(Self(*private_key.sk_sig() + *private_key.r_sig() + compute_key.sk_prf()))
    }
}

impl<N: Network> FromStr for ViewKey<N> {
    type Err = Error;

    /// Reads in an account view key from a base58 string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Encode the string into base58.
        let data = s.from_base58().map_err(|err| anyhow!("{:?}", err))?;
        if data.len() != 39 {
            bail!("Invalid account view key length: found {}, expected 39", data.len())
        } else if data[0..7] != VIEW_KEY_PREFIX {
            bail!("Invalid account view key prefix: found {:?}, expected {:?}", &data[0..7], VIEW_KEY_PREFIX)
        }
        // Output the view key.
        Ok(Self(FromBytes::read_le(&data[7..39])?))
    }
}

impl<N: Network> fmt::Display for ViewKey<N> {
    /// Writes the account view key as a base58 string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Write the view key bytes.
        let mut view_key = [0u8; 39];
        view_key[0..7].copy_from_slice(&VIEW_KEY_PREFIX);
        self.0.write_le(&mut view_key[7..39]).map_err(|_| fmt::Error)?;
        // Encode the view key into base58.
        write!(f, "{}", view_key.to_base58())
    }
}

impl<N: Network> FromBytes for ViewKey<N> {
    /// Reads an account view key from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self(FromBytes::read_le(&mut reader).map_err(|e| error(format!("{e}")))?))
    }
}

impl<N: Network> ToBytes for ViewKey<N> {
    /// Writes an account view key to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<N: Network> Serialize for ViewKey<N> {
    /// Serializes an account view key into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for ViewKey<N> {
    /// Deserializes an account view key from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize(
                deserializer,
                "private key",
                (N::Scalar::size_in_bits() + 7) / 8,
            ),
        }
    }
}

impl<N: Network> Deref for ViewKey<N> {
    type Target = N::Scalar;

    /// Returns the account view key as a scalar.
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{PrivateKey, Testnet3};
    use snarkvm_utilities::test_crypto_rng;

    use anyhow::Result;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_string() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new view key.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let expected = ViewKey::try_from(private_key)?;

            // Check the string representation.
            let candidate = format!("{expected}");
            assert_eq!(expected, ViewKey::from_str(&candidate)?);
        }
        Ok(())
    }

    #[test]
    fn test_serde_json() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new view key.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let expected = ViewKey::try_from(private_key)?;

            // Serialize
            let expected_string = &expected.to_string();
            let candidate_string = serde_json::to_string(&expected)?;
            assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string)?.as_str().unwrap());

            // Deserialize
            assert_eq!(expected, ViewKey::from_str(expected_string)?);
            assert_eq!(expected, serde_json::from_str(&candidate_string)?);
        }
        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new view key.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let expected = ViewKey::try_from(private_key)?;

            // Serialize
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(&expected_bytes[..], &bincode::serialize(&expected)?[..]);

            // Deserialize
            assert_eq!(expected, ViewKey::read_le(&expected_bytes[..])?);
            assert_eq!(expected, bincode::deserialize(&expected_bytes[..])?);
        }
        Ok(())
    }
}
