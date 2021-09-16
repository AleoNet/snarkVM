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

use snarkvm_utilities::{to_bytes_le, ToBytes};

use serde::{Deserialize, Serialize};
use std::fmt::{
    Display,
    Formatter,
    {self},
};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct MerkleRoot(pub [u8; 32]);

impl MerkleRoot {
    pub fn from_element<B: ToBytes>(src: B) -> MerkleRoot {
        let root_bytes = to_bytes_le![src].expect("could not convert element to bytes");
        assert_eq!(root_bytes.len() <= 32);

        let mut merkle_root_bytes = [0u8; 32];
        merkle_root_bytes[..].copy_from_slice(&root_bytes);
        MerkleRoot(merkle_root_bytes)
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
