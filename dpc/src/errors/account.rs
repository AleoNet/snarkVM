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

use snarkvm_algorithms::errors::{CRHError, CommitmentError, EncryptionError, PRFError, SignatureError};

#[derive(Debug, Error)]
pub enum ViewKeyError {
    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),
}

impl From<std::io::Error> for ViewKeyError {
    fn from(error: std::io::Error) -> Self {
        ViewKeyError::Crate("std::io", format!("{:?}", error))
    }
}

impl From<AccountError> for ViewKeyError {
    fn from(error: AccountError) -> Self {
        ViewKeyError::Crate("snarkos_errors::objects::account", format!("{:?}", error))
    }
}

impl From<hex::FromHexError> for ViewKeyError {
    fn from(error: hex::FromHexError) -> Self {
        ViewKeyError::Crate("hex", format!("{:?}", error))
    }
}

impl From<SignatureError> for ViewKeyError {
    fn from(error: SignatureError) -> Self {
        ViewKeyError::Crate("snarkos_errors::algorithms::signature", format!("{:?}", error))
    }
}

#[derive(Debug, Error)]
pub enum PrivateKeyError {
    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),
}

impl From<AccountError> for PrivateKeyError {
    fn from(error: AccountError) -> Self {
        PrivateKeyError::Crate("snarkvm::dpc::errors::account", format!("{:?}", error))
    }
}

impl From<std::io::Error> for PrivateKeyError {
    fn from(error: std::io::Error) -> Self {
        PrivateKeyError::Crate("std::io", format!("{:?}", error))
    }
}

#[derive(Debug, Error)]
pub enum AddressError {
    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),
}

impl From<AccountError> for AddressError {
    fn from(error: AccountError) -> Self {
        AddressError::Crate("snarkvm::dpc::errors::account", format!("{:?}", error))
    }
}

impl From<std::io::Error> for AddressError {
    fn from(error: std::io::Error) -> Self {
        AddressError::Crate("std::io", format!("{:?}", error))
    }
}

#[derive(Debug, Error)]
pub enum AccountError {
    #[error("{}", _0)]
    CommitmentError(CommitmentError),

    #[error("{}", _0)]
    CRHError(CRHError),

    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),

    #[error("{}", _0)]
    EncryptionError(EncryptionError),

    #[error("invalid account commitment")]
    InvalidAccountCommitment,

    #[error("invalid byte length: {}", _0)]
    InvalidByteLength(usize),

    #[error("invalid character length: {}", _0)]
    InvalidCharacterLength(usize),

    #[error("invalid prefix: {:?}", _0)]
    InvalidPrefix(String),

    #[error("invalid prefix bytes: {:?}", _0)]
    InvalidPrefixBytes(Vec<u8>),

    #[error("invalid account private key seed")]
    InvalidPrivateKeySeed,

    #[error("{}", _0)]
    Message(String),

    #[error("{}", _0)]
    PRFError(PRFError),

    #[error("{}", _0)]
    SignatureError(SignatureError),
}

impl From<CommitmentError> for AccountError {
    fn from(error: CommitmentError) -> Self {
        AccountError::CommitmentError(error)
    }
}

impl From<CRHError> for AccountError {
    fn from(error: CRHError) -> Self {
        AccountError::CRHError(error)
    }
}

impl From<EncryptionError> for AccountError {
    fn from(error: EncryptionError) -> Self {
        AccountError::EncryptionError(error)
    }
}

impl From<PRFError> for AccountError {
    fn from(error: PRFError) -> Self {
        AccountError::PRFError(error)
    }
}

impl From<SignatureError> for AccountError {
    fn from(error: SignatureError) -> Self {
        AccountError::SignatureError(error)
    }
}

impl From<base58::FromBase58Error> for AccountError {
    fn from(error: base58::FromBase58Error) -> Self {
        AccountError::Crate("base58", format!("{:?}", error))
    }
}

impl From<bech32::Error> for AccountError {
    fn from(error: bech32::Error) -> Self {
        AccountError::Crate("bech32", format!("{:?}", error))
    }
}

impl From<std::io::Error> for AccountError {
    fn from(error: std::io::Error) -> Self {
        AccountError::Crate("std::io", format!("{:?}", error))
    }
}
