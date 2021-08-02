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

use snarkvm_algorithms::errors::MerkleError;
use snarkvm_dpc::errors::TransactionError;

#[derive(Debug, Error)]
pub enum LedgerError {
    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),

    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),

    #[error("duplicate sn pushed to ledger")]
    DuplicateMemo,

    #[error("duplicate memo pushed to ledger")]
    DuplicateSn,

    #[error("database already exists")]
    ExistingDatabase,

    #[error("invalid cm pushed to ledger")]
    InvalidCm,

    #[error("invalid cm index during proving")]
    InvalidCmIndex,

    #[error("Invalid genesis block header")]
    InvalidGenesisBlockHeader,

    #[error("{}", _0)]
    MerkleError(#[from] MerkleError),

    #[error("{}", _0)]
    Message(String),

    #[error("{}", _0)]
    TransactionError(#[from] TransactionError),
}

impl From<std::io::Error> for LedgerError {
    fn from(error: std::io::Error) -> Self {
        LedgerError::Crate("std::io", format!("{:?}", error))
    }
}
