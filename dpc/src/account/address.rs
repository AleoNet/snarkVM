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

use crate::{account_format, traits::Parameters, AccountError, PrivateKey, ViewKey};
use snarkvm_algorithms::{EncryptionScheme, SignatureScheme};
use snarkvm_curves::AffineCurve;
use snarkvm_utilities::{FromBytes, ToBytes};

use bech32::{self, FromBase32, ToBase32};
use std::{
    convert::TryFrom,
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

#[derive(Derivative)]
#[derivative(
    Default(bound = "C: Parameters"),
    Clone(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct Address<C: Parameters> {
    pub encryption_key: <C::AccountEncryptionScheme as EncryptionScheme>::PublicKey,
}

impl<C: Parameters> Address<C> {
    /// Derives the account address from an account private key.
    pub fn from_private_key(private_key: &PrivateKey<C>) -> Result<Self, AccountError> {
        let decryption_key = private_key.to_decryption_key()?;
        let encryption_key = C::account_encryption_scheme().generate_public_key(&decryption_key)?;
        Ok(Self { encryption_key })
    }

    /// Derives the account address from an account view key.
    pub fn from_view_key(view_key: &ViewKey<C>) -> Result<Self, AccountError> {
        let encryption_key = C::account_encryption_scheme().generate_public_key(&view_key.decryption_key)?;
        Ok(Self { encryption_key })
    }

    /// Verifies a signature on a message signed by the account view key.
    /// Returns `true` if the signature is valid. Otherwise, returns `false`.
    pub fn verify_signature(
        &self,
        message: &[u8],
        signature: &<C::AccountSignatureScheme as SignatureScheme>::Signature,
    ) -> Result<bool, AccountError> {
        let signature_public_key = self.to_signature_public_key()?;
        Ok(C::account_signature_scheme().verify(&signature_public_key, message, signature)?)
    }

    /// Returns the address as a signature public key.
    pub fn to_signature_public_key(&self) -> Result<C::AccountSignaturePublicKey, AccountError> {
        use snarkvm_curves::edwards_bls12::EdwardsAffine;

        let x_coordinate = FromBytes::from_bytes_le(&self.encryption_key.to_bytes_le()?)?;

        if let Some(element) = <EdwardsAffine as AffineCurve>::from_x_coordinate(x_coordinate, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(FromBytes::from_bytes_le(&element.to_bytes_le()?)?);
            }
        }

        if let Some(element) = <EdwardsAffine as AffineCurve>::from_x_coordinate(x_coordinate, false) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(FromBytes::from_bytes_le(&element.to_bytes_le()?)?);
            }
        }

        Err(snarkvm_algorithms::SignatureError::Message("Failed to read signature public key".into()).into())
    }

    /// Returns the address as an encryption public key.
    pub fn to_encryption_key(&self) -> &<C::AccountEncryptionScheme as EncryptionScheme>::PublicKey {
        &self.encryption_key
    }
}

impl<C: Parameters> TryFrom<PrivateKey<C>> for Address<C> {
    type Error = AccountError;

    /// Derives the account address from an account private key.
    fn try_from(private_key: PrivateKey<C>) -> Result<Self, Self::Error> {
        Self::try_from(&private_key)
    }
}

impl<C: Parameters> TryFrom<&PrivateKey<C>> for Address<C> {
    type Error = AccountError;

    /// Derives the account address from an account private key.
    fn try_from(private_key: &PrivateKey<C>) -> Result<Self, Self::Error> {
        Self::from_private_key(private_key)
    }
}

impl<C: Parameters> TryFrom<ViewKey<C>> for Address<C> {
    type Error = AccountError;

    /// Derives the account address from an account view key.
    fn try_from(view_key: ViewKey<C>) -> Result<Self, Self::Error> {
        Self::try_from(&view_key)
    }
}

impl<C: Parameters> TryFrom<&ViewKey<C>> for Address<C> {
    type Error = AccountError;

    /// Derives the account address from an account view key.
    fn try_from(view_key: &ViewKey<C>) -> Result<Self, Self::Error> {
        Self::from_view_key(view_key)
    }
}

impl<C: Parameters> FromStr for Address<C> {
    type Err = AccountError;

    /// Reads in an account address string.
    fn from_str(address: &str) -> Result<Self, Self::Err> {
        if address.len() != 63 {
            return Err(AccountError::InvalidCharacterLength(address.len()));
        }

        let prefix = &address.to_lowercase()[0..4];
        if prefix != account_format::ADDRESS_PREFIX {
            return Err(AccountError::InvalidPrefix(prefix.to_string()));
        };

        let (_hrp, data, _variant) = bech32::decode(&address)?;
        if data.is_empty() {
            return Err(AccountError::InvalidByteLength(0));
        }

        let buffer = Vec::from_base32(&data)?;
        Ok(Self::read_le(&buffer[..])?)
    }
}

impl<C: Parameters> FromBytes for Address<C> {
    /// Reads in an account address buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let encryption_key: <C::AccountEncryptionScheme as EncryptionScheme>::PublicKey =
            FromBytes::read_le(&mut reader)?;

        Ok(Self { encryption_key })
    }
}

impl<C: Parameters> ToBytes for Address<C> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.encryption_key.write_le(&mut writer)
    }
}

impl<C: Parameters> fmt::Display for Address<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Write the encryption key to a buffer.
        let mut address = [0u8; 32];
        self.encryption_key
            .write_le(&mut address[0..32])
            .expect("address formatting failed");

        bech32::encode(
            &account_format::ADDRESS_PREFIX.to_string(),
            address.to_base32(),
            bech32::Variant::Bech32,
        )
        .unwrap()
        .fmt(f)
    }
}

impl<C: Parameters> fmt::Debug for Address<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Address {{ encryption_key: {:?} }}", self.encryption_key)
    }
}
