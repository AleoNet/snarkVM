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

use crate::Network;
use snarkvm_curves::AffineCurve;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{error, FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::{bail, Error};
use bech32::{self, FromBase32, ToBase32};
use core::{fmt, str};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::io::{Read, Result as IoResult, Write};

static ADDRESS_PREFIX: &str = "aleo";

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Address<N: Network>(N::Affine);

// use crate::{account_format, AccountError, ComputeKey, PrivateKey, ViewKey};
// use snarkvm_algorithms::{EncryptionScheme, SignatureScheme};
// use snarkvm_curves::AffineCurve;

// impl<N: Network> Address<N> {
// /// Derives the account address from an account private key.
// pub fn from_private_key(private_key: &PrivateKey<N>) -> Self {
//     Self::from_compute_key(&private_key.to_compute_key())
// }
//
// /// Derives the account address from an account compute key.
// pub fn from_compute_key(compute_key: &ComputeKey<N>) -> Self {
//     Self(compute_key.to_encryption_key())
// }
//
// /// Derives the account address from an account view key.
// pub fn from_view_key(view_key: &ViewKey<N>) -> Self {
//     // TODO (howardwu): This operation can be optimized by precomputing powers in ECIES native impl.
//     //  Optimizing this will also speed up encryption.
//     Self(N::account_encryption_scheme().generate_public_key(&*view_key))
// }
//
// /// Verifies a signature on a message signed by the account view key.
// /// Returns `true` if the signature is valid. Otherwise, returns `false`.
// pub fn verify_signature(&self, message: &[bool], signature: &N::AccountSignature) -> Result<bool, AccountError> {
//     Ok(N::account_signature_scheme().verify(&self.0, message, signature)?)
// }
// }

// impl<N: Network> From<PrivateKey<N>> for Address<N> {
//     /// Derives the account address from an account private key.
//     fn from(private_key: PrivateKey<N>) -> Self {
//         Self::from(&private_key)
//     }
// }
//
// impl<N: Network> From<&PrivateKey<N>> for Address<N> {
//     /// Derives the account address from an account private key.
//     fn from(private_key: &PrivateKey<N>) -> Self {
//         Self::from_private_key(private_key)
//     }
// }
//
// impl<N: Network> From<ComputeKey<N>> for Address<N> {
//     /// Derives the account address from an account compute key.
//     fn from(compute_key: ComputeKey<N>) -> Self {
//         Self::from(&compute_key)
//     }
// }
//
// impl<N: Network> From<&ComputeKey<N>> for Address<N> {
//     /// Derives the account address from an account compute key.
//     fn from(compute_key: &ComputeKey<N>) -> Self {
//         Self::from_compute_key(compute_key)
//     }
// }
//
// impl<N: Network> From<ViewKey<N>> for Address<N> {
//     /// Derives the account address from an account view key.
//     fn from(view_key: ViewKey<N>) -> Self {
//         Self::from(&view_key)
//     }
// }
//
// impl<N: Network> From<&ViewKey<N>> for Address<N> {
//     /// Derives the account address from an account view key.
//     fn from(view_key: &ViewKey<N>) -> Self {
//         Self::from_view_key(view_key)
//     }
// }

impl<N: Network> str::FromStr for Address<N> {
    type Err = Error;

    /// Reads in an account address string.
    fn from_str(address: &str) -> Result<Self, Self::Err> {
        // Ensure the address string length is 63 characters.
        if address.len() != 63 {
            bail!("Invalid account address length: found {}, expected 63", address.len())
        }
        // Decode the address string from bech32m.
        let (hrp, data, variant) = bech32::decode(address)?;
        if hrp != ADDRESS_PREFIX {
            bail!("Failed to decode address: '{hrp}' is an invalid prefix")
        } else if data.is_empty() {
            bail!("Failed to decode address: data field is empty")
        } else if variant != bech32::Variant::Bech32m {
            bail!("Found an address that is not bech32m encoded: {address}");
        }
        // Decode the address data from u5 to u8.
        let buffer = Vec::from_base32(&data)?;
        // Deserialize the address data into an account address.
        Ok(Self::read_le(&buffer[..])?)
    }
}

impl<N: Network> fmt::Display for Address<N> {
    /// Writes an account address as a bech32m string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Convert the address to bytes.
        let bytes = self.to_bytes_le().map_err(|_| fmt::Error)?;
        // Encode the bytes into bech32m.
        bech32::encode(ADDRESS_PREFIX, bytes.to_base32(), bech32::Variant::Bech32m).map_err(|_| fmt::Error)?.fmt(f)
    }
}

impl<N: Network> FromBytes for Address<N> {
    /// Reads in an account address from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let x_coordinate = N::Field::read_le(&mut reader)?;
        Ok(Self(N::affine_from_x_coordinate(x_coordinate).map_err(|err| error(format!("{err}")))?))
    }
}

impl<N: Network> ToBytes for Address<N> {
    /// Writes an account address to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.to_x_coordinate().write_le(&mut writer)
    }
}

impl<N: Network> Serialize for Address<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Address<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => str::FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => {
                FromBytesDeserializer::<Self>::deserialize(deserializer, "address", (N::Field::size_in_bits() + 7) / 8)
            }
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::{Testnet3, PrivateKey};
//     use snarkvm_utilities::test_crypto_rng;
//
//     use anyhow::Result;
//     use core::str::FromStr;
//
//     type CurrentNetwork = Testnet3;
//
//     #[test]
//     fn test_serde_json() -> Result<()> {
//         let private_key = PrivateKey::new(&mut test_crypto_rng());
//         let expected_address: Address<CurrentNetwork> = private_key.into();
//
//         // Serialize
//         let expected_string = &expected_address.to_string();
//         let candidate_string = serde_json::to_string(&expected_address)?;
//         assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string)?.as_str()?);
//
//         // Deserialize
//         assert_eq!(expected_address, Address::from_str(expected_string)?);
//         assert_eq!(expected_address, serde_json::from_str(&candidate_string)?);
//
//         Ok(())
//     }
//
//     #[test]
//     fn test_bincode() -> Result<()> {
//         let private_key = PrivateKey::new(&mut test_crypto_rng());
//         let expected_address: Address<CurrentNetwork> = private_key.into();
//
//         // Serialize
//         let expected_bytes = expected_address.to_bytes_le()?;
//         assert_eq!(&expected_bytes[..], &bincode::serialize(&expected_address)?[..]);
//
//         // Deserialize
//         assert_eq!(expected_address, Address::read_le(&expected_bytes[..])?);
//         assert_eq!(expected_address, bincode::deserialize(&expected_bytes[..])?);
//
//         Ok(())
//     }
// }
