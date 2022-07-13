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

use crate::{account_format, AccountError, ComputeKey, Network, PrivateKey, ViewKey};
use snarkvm_algorithms::{EncryptionScheme, SignatureScheme};
use snarkvm_curves::AffineCurve;
use snarkvm_utilities::{
    fmt,
    io::{Read, Result as IoResult, Write},
    ops::Deref,
    str::FromStr,
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
};

use bech32::{self, FromBase32, ToBase32};
use core::hash::{Hash, Hasher};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

pub struct Address<N: Network>(<N::AccountEncryptionScheme as EncryptionScheme>::PublicKey);

impl<N: Network> Address<N> {
    /// Derives the account address from an account private key.
    pub fn from_private_key(private_key: &PrivateKey<N>) -> Self {
        Self::from_compute_key(&private_key.to_compute_key())
    }

    /// Derives the account address from an account compute key.
    pub fn from_compute_key(compute_key: &ComputeKey<N>) -> Self {
        Self(compute_key.to_encryption_key())
    }

    /// Derives the account address from an account view key.
    pub fn from_view_key(view_key: &ViewKey<N>) -> Self {
        // TODO (howardwu): This operation can be optimized by precomputing powers in ECIES native impl.
        //  Optimizing this will also speed up encryption.
        Self(N::account_encryption_scheme().generate_public_key(view_key))
    }

    /// Verifies a signature on a message signed by the account view key.
    /// Returns `true` if the signature is valid. Otherwise, returns `false`.
    pub fn verify_signature(&self, message: &[bool], signature: &N::AccountSignature) -> Result<bool, AccountError> {
        Ok(N::account_signature_scheme().verify(&self.0, message, signature)?)
    }
}

impl<N: Network> From<PrivateKey<N>> for Address<N> {
    /// Derives the account address from an account private key.
    fn from(private_key: PrivateKey<N>) -> Self {
        Self::from(&private_key)
    }
}

impl<N: Network> From<&PrivateKey<N>> for Address<N> {
    /// Derives the account address from an account private key.
    fn from(private_key: &PrivateKey<N>) -> Self {
        Self::from_private_key(private_key)
    }
}

impl<N: Network> From<ComputeKey<N>> for Address<N> {
    /// Derives the account address from an account compute key.
    fn from(compute_key: ComputeKey<N>) -> Self {
        Self::from(&compute_key)
    }
}

impl<N: Network> From<&ComputeKey<N>> for Address<N> {
    /// Derives the account address from an account compute key.
    fn from(compute_key: &ComputeKey<N>) -> Self {
        Self::from_compute_key(compute_key)
    }
}

impl<N: Network> From<ViewKey<N>> for Address<N> {
    /// Derives the account address from an account view key.
    fn from(view_key: ViewKey<N>) -> Self {
        Self::from(&view_key)
    }
}

impl<N: Network> From<&ViewKey<N>> for Address<N> {
    /// Derives the account address from an account view key.
    fn from(view_key: &ViewKey<N>) -> Self {
        Self::from_view_key(view_key)
    }
}

impl<N: Network> FromBytes for Address<N> {
    /// Reads in an account address buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let x_coordinate = N::InnerScalarField::read_le(&mut reader)?;

        if let Some(element) = N::ProgramAffineCurve::from_x_coordinate(x_coordinate, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(Self(element));
            }
        }

        if let Some(element) = N::ProgramAffineCurve::from_x_coordinate(x_coordinate, false) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(Self(element));
            }
        }

        Err(AccountError::Message("Failed to read encryption public key address".into()).into())
    }
}

impl<N: Network> ToBytes for Address<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.to_x_coordinate().write_le(&mut writer)
    }
}

impl<N: Network> FromStr for Address<N> {
    type Err = AccountError;

    /// Reads in an account address string.
    fn from_str(address: &str) -> Result<Self, Self::Err> {
        if address.len() != 63 {
            return Err(AccountError::InvalidCharacterLength(address.len()));
        }

        let (hrp, data, variant) = bech32::decode(address)?;
        if hrp != account_format::ADDRESS_PREFIX {
            return Err(AccountError::InvalidPrefix(hrp));
        }
        if data.is_empty() {
            return Err(AccountError::InvalidByteLength(0));
        }

        let buffer = Vec::from_base32(&data)?;
        let address = Self::read_le(&buffer[..])?;

        if variant != bech32::Variant::Bech32m {
            eprintln!(
                "[Warning] This Aleo address is in bech32 (deprecated) and should be encoded in bech32m as:\n{}",
                address
            );
        }

        Ok(address)
    }
}

impl<N: Network> fmt::Display for Address<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Convert the encryption key to bytes.
        let encryption_key = self.to_bytes_le().expect("Failed to write encryption key as bytes");

        bech32::encode(account_format::ADDRESS_PREFIX, encryption_key.to_base32(), bech32::Variant::Bech32m)
            .expect("Failed to encode in bech32m")
            .fmt(f)
    }
}

impl<N: Network> fmt::Debug for Address<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Address {{ encryption_key: {:?} }}", self.0)
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
            false => FromBytesDeserializer::<Self>::deserialize(deserializer, "address", N::ADDRESS_SIZE_IN_BYTES),
        }
    }
}

impl<N: Network> Copy for Address<N> {}

impl<N: Network> Clone for Address<N> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<N: Network> PartialEq for Address<N> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<N: Network> Eq for Address<N> {}

impl<N: Network> Hash for Address<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<N: Network> Default for Address<N> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<N: Network> Deref for Address<N> {
    type Target = <N::AccountEncryptionScheme as EncryptionScheme>::PublicKey;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;

    use rand::thread_rng;

    #[test]
    fn test_serde_json() {
        let rng = &mut thread_rng();

        let private_key = PrivateKey::new(rng);
        let expected_address: Address<Testnet2> = private_key.into();

        // Serialize
        let expected_string = &expected_address.to_string();
        let candidate_string = serde_json::to_string(&expected_address).unwrap();
        assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string).unwrap().as_str().unwrap());

        // Deserialize
        assert_eq!(expected_address, Address::from_str(expected_string).unwrap());
        assert_eq!(expected_address, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_bincode() {
        let rng = &mut thread_rng();

        let private_key = PrivateKey::new(rng);
        let expected_address: Address<Testnet2> = private_key.into();

        // Serialize
        let expected_bytes = expected_address.to_bytes_le().unwrap();
        assert_eq!(&expected_bytes[..], &bincode::serialize(&expected_address).unwrap()[..]);

        // Deserialize
        assert_eq!(expected_address, Address::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_address, bincode::deserialize(&expected_bytes[..]).unwrap());
    }
}
