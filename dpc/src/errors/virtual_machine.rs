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

use snarkvm_algorithms::{CRHError, MerkleError, SNARKError};
use snarkvm_fields::ConstraintFieldError;
use snarkvm_parameters::ParameterError;

#[derive(Debug, Error)]
pub enum VMError {
    #[error("{}", _0)]
    AccountError(#[from] crate::AccountError),

    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),

    #[error("Insufficient balance")]
    BalanceInsufficient,

    #[error("Balance overflowed")]
    BalanceOverflow,

    #[error("Balance overwritten")]
    BalanceOverwritten,

    #[error("Cannot verify the provided record commitment")]
    CannotVerifyCommitment,

    #[error("{}", _0)]
    ConstraintFieldError(#[from] ConstraintFieldError),

    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),

    #[error("{}", _0)]
    CRHError(#[from] CRHError),

    #[error("{}", _0)]
    FromHexError(#[from] hex::FromHexError),

    #[error("Given private key does not correspond to the record owner")]
    IncorrectPrivateKey,

    #[error("{}", _0)]
    MerkleError(#[from] MerkleError),

    #[error("Missing caller {}", _0)]
    MissingCaller(String),

    #[error("{}", _0)]
    ParameterError(#[from] ParameterError),

    #[error("{}", _0)]
    SNARKError(#[from] SNARKError),
}

impl From<std::io::Error> for VMError {
    fn from(error: std::io::Error) -> Self {
        VMError::Crate("std::io", format!("{:?}", error))
    }
}

impl From<VMError> for std::io::Error {
    fn from(error: VMError) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", error))
    }
}
