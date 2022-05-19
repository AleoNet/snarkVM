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

use crate::{ComputeKey, Network, PrivateKey, ViewKey};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
};

use anyhow::{bail, Error};
use bech32::{self, FromBase32, ToBase32};
use core::{fmt, ops::Deref, str::FromStr};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

static ADDRESS_PREFIX: &str = "aleo";

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Address<N: Network>(N::Affine);

impl<N: Network> TryFrom<PrivateKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account private key.
    fn try_from(private_key: PrivateKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&private_key)
    }
}

impl<N: Network> TryFrom<&PrivateKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account private key.
    fn try_from(private_key: &PrivateKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(ViewKey::try_from(private_key)?)
    }
}

impl<N: Network> TryFrom<ComputeKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account compute key.
    fn try_from(compute_key: ComputeKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&compute_key)
    }
}

impl<N: Network> TryFrom<&ComputeKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account compute key.
    fn try_from(compute_key: &ComputeKey<N>) -> Result<Self, Self::Error> {
        // Compute pk_prf := G^sk_prf.
        let pk_prf = N::g_scalar_multiply(compute_key.sk_prf());
        // Compute the address := pk_sig + pr_sig + pk_prf.
        Ok(Self((compute_key.pk_sig().to_projective() + compute_key.pr_sig().to_projective() + pk_prf).to_affine()))
    }
}

impl<N: Network> TryFrom<ViewKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account view key.
    fn try_from(view_key: ViewKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&view_key)
    }
}

impl<N: Network> TryFrom<&ViewKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account view key.
    fn try_from(view_key: &ViewKey<N>) -> Result<Self, Self::Error> {
        Ok(Self(N::g_scalar_multiply(&**view_key).to_affine()))
    }
}

// /// Verifies a signature on a message signed by the account view key.
// /// Returns `true` if the signature is valid. Otherwise, returns `false`.
// pub fn verify_signature(&self, message: &[bool], signature: &N::AccountSignature) -> Result<bool, AccountError> {
//     Ok(N::account_signature_scheme().verify(&self.0, message, signature)?)
// }
// }

impl<N: Network> FromStr for Address<N> {
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
        Ok(Self(N::affine_from_x_coordinate(x_coordinate).map_err(|e| error(format!("{e}")))?))
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
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => {
                FromBytesDeserializer::<Self>::deserialize(deserializer, "address", (N::Field::size_in_bits() + 7) / 8)
            }
        }
    }
}

impl<N: Network> Deref for Address<N> {
    type Target = N::Affine;

    /// Returns the address as an affine group element.
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
    use core::str::FromStr;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_serde_json() -> Result<()> {
        let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
        let expected_address = Address::try_from(private_key)?;

        // Serialize
        let expected_string = &expected_address.to_string();
        let candidate_string = serde_json::to_string(&expected_address)?;
        assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string)?.as_str().unwrap());

        // Deserialize
        assert_eq!(expected_address, Address::from_str(expected_string)?);
        assert_eq!(expected_address, serde_json::from_str(&candidate_string)?);

        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
        let expected_address = Address::try_from(private_key)?;

        // Serialize
        let expected_bytes = expected_address.to_bytes_le()?;
        assert_eq!(&expected_bytes[..], &bincode::serialize(&expected_address)?[..]);

        // Deserialize
        assert_eq!(expected_address, Address::read_le(&expected_bytes[..])?);
        assert_eq!(expected_address, bincode::deserialize(&expected_bytes[..])?);

        Ok(())
    }
}
