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

use crate::{account_format, AccountError, Network, PrivateKey};
use snarkvm_algorithms::EncryptionScheme;
use snarkvm_utilities::{FromBytes, ToBytes};

use base58::{FromBase58, ToBase58};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    ops::Deref,
    str::FromStr,
};

#[derive(Clone, PartialEq, Eq)]
pub struct ViewKey<N: Network>(<N::AccountEncryptionScheme as EncryptionScheme>::PrivateKey);

impl<N: Network> ViewKey<N> {
    /// Creates a new account view key from an account private key.
    pub fn from_private_key(private_key: &PrivateKey<N>) -> Self {
        Self(private_key.to_decryption_key())
    }
}

impl<N: Network> From<PrivateKey<N>> for ViewKey<N> {
    /// Creates a new account view key from an account private key.
    fn from(private_key: PrivateKey<N>) -> Self {
        Self::from(&private_key)
    }
}

impl<N: Network> From<&PrivateKey<N>> for ViewKey<N> {
    /// Creates a new account view key from an account private key.
    fn from(private_key: &PrivateKey<N>) -> Self {
        Self::from_private_key(private_key)
    }
}

impl<N: Network> FromStr for ViewKey<N> {
    type Err = AccountError;

    /// Reads in an account view key string.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let data = s.from_base58()?;
        if data.len() != 39 {
            return Err(AccountError::InvalidByteLength(data.len()));
        }

        if data[0..7] != account_format::VIEW_KEY_PREFIX {
            return Err(AccountError::InvalidPrefixBytes(data[0..7].to_vec()));
        }

        Ok(Self(FromBytes::read_le(&data[7..])?))
    }
}

impl<N: Network> FromBytes for ViewKey<N> {
    /// Reads in an account view key buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self(FromBytes::read_le(&mut reader)?))
    }
}

impl<N: Network> ToBytes for ViewKey<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<N: Network> fmt::Display for ViewKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut view_key = [0u8; 39];
        view_key[0..7].copy_from_slice(&account_format::VIEW_KEY_PREFIX);
        self.0.write_le(&mut view_key[7..39]).expect("view key formatting failed");

        write!(f, "{}", view_key.to_base58())
    }
}

impl<N: Network> fmt::Debug for ViewKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ViewKey {{ decryption_key: {:?} }}", self.0)
    }
}

impl<N: Network> Deref for ViewKey<N> {
    type Target = <N::AccountEncryptionScheme as EncryptionScheme>::PrivateKey;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
