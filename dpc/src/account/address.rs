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

use crate::{account_format, AccountError, ComputeKey, Network, PrivateKey, ViewKey};
use snarkvm_algorithms::{EncryptionScheme, SignatureScheme};
use snarkvm_curves::AffineCurve;
use snarkvm_utilities::{FromBytes, ToBytes};

use bech32::{self, FromBase32, ToBase32};
use std::{
    convert::TryFrom,
    fmt,
    io::{Read, Result as IoResult, Write},
    ops::Deref,
    str::FromStr,
};

#[derive(Derivative)]
#[derivative(
    Default(bound = "N: Network"),
    Copy(bound = "N: Network"),
    Clone(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Address<N: Network>(<N::AccountEncryptionScheme as EncryptionScheme>::PublicKey);

impl<N: Network> Address<N> {
    /// Derives the account address from an account private key.
    pub fn from_private_key(private_key: &PrivateKey<N>) -> Result<Self, AccountError> {
        Self::from_compute_key(&private_key.to_compute_key()?)
    }

    /// Derives the account address from an account compute key.
    pub fn from_compute_key(compute_key: &ComputeKey<N>) -> Result<Self, AccountError> {
        Ok(Self(compute_key.to_encryption_key()?))
    }

    /// Derives the account address from an account view key.
    pub fn from_view_key(view_key: &ViewKey<N>) -> Result<Self, AccountError> {
        // TODO (howardwu): This operation can be optimized by precomputing powers in ECIES native impl.
        //  Optimizing this will also speed up encryption.
        Ok(Self(N::account_encryption_scheme().generate_public_key(&*view_key)?))
    }

    /// Verifies a signature on a message signed by the account view key.
    /// Returns `true` if the signature is valid. Otherwise, returns `false`.
    pub fn verify_signature(&self, message: &[u8], signature: &N::AccountSignature) -> Result<bool, AccountError> {
        Ok(N::account_signature_scheme().verify(&self.0, message, signature)?)
    }
}

impl<N: Network> TryFrom<PrivateKey<N>> for Address<N> {
    type Error = AccountError;

    /// Derives the account address from an account private key.
    fn try_from(private_key: PrivateKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&private_key)
    }
}

impl<N: Network> TryFrom<&PrivateKey<N>> for Address<N> {
    type Error = AccountError;

    /// Derives the account address from an account private key.
    fn try_from(private_key: &PrivateKey<N>) -> Result<Self, Self::Error> {
        Self::from_private_key(private_key)
    }
}

impl<N: Network> TryFrom<ComputeKey<N>> for Address<N> {
    type Error = AccountError;

    /// Derives the account address from an account compute key.
    fn try_from(compute_key: ComputeKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&compute_key)
    }
}

impl<N: Network> TryFrom<&ComputeKey<N>> for Address<N> {
    type Error = AccountError;

    /// Derives the account address from an account compute key.
    fn try_from(compute_key: &ComputeKey<N>) -> Result<Self, Self::Error> {
        Self::from_compute_key(compute_key)
    }
}

impl<N: Network> TryFrom<ViewKey<N>> for Address<N> {
    type Error = AccountError;

    /// Derives the account address from an account view key.
    fn try_from(view_key: ViewKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&view_key)
    }
}

impl<N: Network> TryFrom<&ViewKey<N>> for Address<N> {
    type Error = AccountError;

    /// Derives the account address from an account view key.
    fn try_from(view_key: &ViewKey<N>) -> Result<Self, Self::Error> {
        Self::from_view_key(view_key)
    }
}

impl<N: Network> FromBytes for Address<N> {
    /// Reads in an account address buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let x_coordinate = N::ProgramBaseField::read_le(&mut reader)?;

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

impl<N: Network> fmt::Display for Address<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Write the encryption key to a buffer.
        let mut encryption_key = [0u8; 32];
        self.write_le(&mut encryption_key[0..32])
            .expect("Failed to write encryption key as bytes");

        bech32::encode(
            &account_format::ADDRESS_PREFIX.to_string(),
            encryption_key.to_base32(),
            bech32::Variant::Bech32,
        )
        .expect("Failed to encode in bech32")
        .fmt(f)
    }
}

impl<N: Network> fmt::Debug for Address<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Address {{ encryption_key: {:?} }}", self.0)
    }
}

impl<N: Network> Deref for Address<N> {
    type Target = <N::AccountEncryptionScheme as EncryptionScheme>::PublicKey;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
