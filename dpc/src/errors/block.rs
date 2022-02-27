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

use std::fmt::Debug;

#[derive(Debug, Error)]
pub enum BlockError {
    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),

    #[error("block already exists {}", _0)]
    BlockExists(String),

    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),

    #[error("{}", _0)]
    CRHError(#[from] snarkvm_algorithms::CRHError),

    #[error("{}", _0)]
    MerkleError(#[from] snarkvm_algorithms::MerkleError),

    #[error("{}", _0)]
    Message(String),
}

impl From<std::io::Error> for BlockError {
    fn from(error: std::io::Error) -> Self {
        BlockError::Crate("std::io", format!("{:?}", error))
    }
}

impl From<BlockError> for std::io::Error {
    fn from(error: BlockError) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, format!("{}", error))
    }
}
