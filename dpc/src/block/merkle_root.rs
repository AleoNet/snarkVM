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

use snarkvm_utilities::ToBytes;

use serde::{Deserialize, Serialize};
use std::fmt::{
    Display,
    Formatter,
    {self},
};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct MerkleRoot(pub [u8; 32]);

impl MerkleRoot {
    pub fn new(root: &[u8]) -> Self {
        assert_eq!(root.len(), 32);
        let mut buffer = [0u8; 32];
        buffer.copy_from_slice(&root);
        Self(buffer)
    }

    pub fn from_element<B: ToBytes>(digest: B) -> MerkleRoot {
        let digest_bytes = digest.to_bytes_le().expect("could not convert digest to bytes");
        assert_eq!(digest_bytes.len(), 32);

        let mut buffer = [0u8; 32];
        buffer[..].copy_from_slice(&digest_bytes);
        MerkleRoot(buffer)
    }

    pub const fn size() -> usize {
        32
    }
}

impl Display for MerkleRoot {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", hex::encode(self.0))
    }
}
