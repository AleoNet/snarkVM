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

use crate::{LoadableMerkleParameters, MerkleParameters, CRH};

/// Defines a Merkle tree using the provided hash and depth.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MerkleTreeParameters<H: CRH, const DEPTH: usize>(H);

impl<H: CRH, const DEPTH: usize> MerkleParameters for MerkleTreeParameters<H, DEPTH> {
    type H = H;

    const DEPTH: usize = DEPTH;

    fn setup(message: &str) -> Self {
        Self(Self::H::setup(message))
    }

    fn crh(&self) -> &Self::H {
        &self.0
    }
}

impl<H: CRH, const DEPTH: usize> From<H> for MerkleTreeParameters<H, DEPTH> {
    fn from(crh: H) -> Self {
        Self(crh)
    }
}

impl<H: CRH, const DEPTH: usize> LoadableMerkleParameters for MerkleTreeParameters<H, DEPTH> {}
