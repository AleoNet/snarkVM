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

#[derive(Debug, Error)]
pub enum AccountError {
    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),

    #[error("{}", _0)]
    Bech32Error(#[from] bech32::Error),

    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),

    #[error("invalid byte length: {}", _0)]
    InvalidByteLength(usize),

    #[error("invalid character length: {}", _0)]
    InvalidCharacterLength(usize),

    #[error("invalid prefix: {:?}", _0)]
    InvalidPrefix(String),

    #[error("invalid prefix bytes: {:?}", _0)]
    InvalidPrefixBytes(Vec<u8>),

    #[error("invalid variant")]
    InvalidVariant,

    #[error("{}", _0)]
    Message(String),
}

impl From<base58::FromBase58Error> for AccountError {
    fn from(error: base58::FromBase58Error) -> Self {
        AccountError::Crate("base58", format!("{:?}", error))
    }
}

impl From<std::io::Error> for AccountError {
    fn from(error: std::io::Error) -> Self {
        AccountError::Crate("std::io", format!("{:?}", error))
    }
}

impl From<AccountError> for std::io::Error {
    fn from(error: AccountError) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", error))
    }
}
