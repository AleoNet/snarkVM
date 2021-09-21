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

#[derive(Debug, Error)]
pub enum MerkleTrieError {
    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),

    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),

    #[error("{}", _0)]
    CRHError(#[from] crate::CRHError),

    #[error("Incorrect key: {:?}", _0)]
    IncorrectKey(Vec<u8>),

    #[error("{}", _0)]
    Message(String),

    #[error("Missing value  at key: {:?}", _0)]
    MissingLeaf(Vec<u8>),
}

impl From<std::io::Error> for MerkleTrieError {
    fn from(error: std::io::Error) -> Self {
        MerkleTrieError::Crate("std::io", format!("{:?}", error))
    }
}
