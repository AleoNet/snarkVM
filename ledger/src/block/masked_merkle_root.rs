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

use crate::Network;
use snarkvm_algorithms::merkle_tree::MerkleTree;
use snarkvm_curves::bls12_377::Fr;
use snarkvm_utilities::ToBytes;

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::{
    fmt::{
        Display,
        Formatter,
        {self},
    },
    sync::Arc,
};

/// A Masked Merkle Root.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct MaskedMerkleRoot(pub [u8; 32]);

impl MaskedMerkleRoot {
    pub fn new(root: &[u8]) -> Self {
        assert_eq!(root.len(), 32);

        let mut buffer = [0u8; 32];
        buffer.copy_from_slice(&root);
        Self(buffer)
    }

    /// Returns the masked Merkle root for the given leaves.
    pub fn from_leaves<N: Network>(leaves: &[[u8; 32]]) -> Result<Self> {
        let tree = MerkleTree::<N::MaskedMerkleTreeParameters>::new(
            Arc::new(N::masked_merkle_tree_parameters().clone()),
            leaves,
        )?;

        let mut buffer = [0u8; 32];
        buffer[..].copy_from_slice(&tree.root().to_bytes_le()?[..]);
        Ok(Self(buffer))
    }

    pub const fn size() -> usize {
        32
    }
}

impl From<Fr> for MaskedMerkleRoot {
    fn from(root: Fr) -> MaskedMerkleRoot {
        let root_bytes = root.to_bytes_le().expect("Failed to convert root to bytes");
        assert_eq!(root_bytes.len(), 32);

        let mut buffer = [0u8; 32];
        buffer[..].copy_from_slice(&root_bytes);
        MaskedMerkleRoot(buffer)
    }
}

impl Display for MaskedMerkleRoot {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", hex::encode(self.0))
    }
}
