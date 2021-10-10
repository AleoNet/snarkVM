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

use std::fmt::Debug;

#[derive(Debug, Error)]
pub enum TransactionError {
    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),

    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),

    #[error(
        "Invalid transition: |serial numbers| = {}, |commitments| = {}, |ciphertexts| = {}",
        _0,
        _1,
        _2
    )]
    InvalidTransition(usize, usize, usize),

    #[error("{}", _0)]
    Message(String),
}

impl From<&'static str> for TransactionError {
    fn from(msg: &'static str) -> Self {
        TransactionError::Message(msg.into())
    }
}

impl From<hex::FromHexError> for TransactionError {
    fn from(error: hex::FromHexError) -> Self {
        TransactionError::Crate("hex", format!("{:?}", error))
    }
}

impl From<std::num::ParseIntError> for TransactionError {
    fn from(error: std::num::ParseIntError) -> Self {
        TransactionError::Crate("std::num", format!("{:?}", error))
    }
}

impl From<std::str::ParseBoolError> for TransactionError {
    fn from(error: std::str::ParseBoolError) -> Self {
        TransactionError::Crate("std::str", format!("{:?}", error))
    }
}

impl From<std::io::Error> for TransactionError {
    fn from(error: std::io::Error) -> Self {
        TransactionError::Crate("std::io", format!("{:?}", error))
    }
}

impl From<TransactionError> for std::io::Error {
    fn from(error: TransactionError) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", error))
    }
}
