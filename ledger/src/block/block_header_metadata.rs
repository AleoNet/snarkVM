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

use snarkvm_utilities::{FromBytes, ToBytes};

use serde::{Deserialize, Serialize};
use std::{
    io::{Read, Result as IoResult, Write},
    mem::size_of,
};

/// Block header metadata.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct BlockHeaderMetadata {
    /// The block timestamp is a Unix epoch time (UTC) when the miner
    /// started hashing the header (according to the miner). - 8 bytes
    timestamp: i64,
    /// Proof of work algorithm difficulty target for this block - 8 bytes
    difficulty_target: u64,
    /// Nonce for solving the PoW puzzle - 4 bytes
    nonce: u32,
}

impl BlockHeaderMetadata {
    /// Initializes a new instance of a block header metadata.
    pub fn new(timestamp: i64, difficulty_target: u64, nonce: u32) -> Self {
        Self {
            timestamp,
            difficulty_target,
            nonce,
        }
    }

    /// Returns the block timestamp.
    pub const fn timestamp(&self) -> i64 {
        self.timestamp
    }

    /// Returns the block difficulty target.
    pub const fn difficulty_target(&self) -> u64 {
        self.difficulty_target
    }

    /// Returns the block nonce.
    pub const fn nonce(&self) -> u32 {
        self.nonce
    }

    /// Returns the size (in bytes) of a block header's metadata.
    pub const fn size() -> usize {
        size_of::<i64>() + size_of::<u64>() + size_of::<u32>()
    }
}

impl FromBytes for BlockHeaderMetadata {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let timestamp = <[u8; 8]>::read_le(&mut reader)?;
        let difficulty_target = <[u8; 8]>::read_le(&mut reader)?;
        let nonce = <[u8; 4]>::read_le(&mut reader)?;

        Ok(Self {
            timestamp: i64::from_le_bytes(timestamp),
            difficulty_target: u64::from_le_bytes(difficulty_target),
            nonce: u32::from_le_bytes(nonce),
        })
    }
}

impl ToBytes for BlockHeaderMetadata {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.timestamp.to_le_bytes().write_le(&mut writer)?;
        self.difficulty_target.to_le_bytes().write_le(&mut writer)?;
        self.nonce.to_le_bytes().write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use chrono::Utc;

    #[test]
    fn test_block_header_metadata_serialization() {
        let block_header_metadata = BlockHeaderMetadata {
            timestamp: Utc::now().timestamp(),
            difficulty_target: 0u64,
            nonce: 0u32,
        };

        let serialized = block_header_metadata.to_bytes_le().unwrap();
        assert_eq!(
            &serialized[..],
            &bincode::serialize(&block_header_metadata).unwrap()[..]
        );

        let deserialized = BlockHeaderMetadata::read_le(&serialized[..]).unwrap();
        assert_eq!(deserialized, block_header_metadata);
    }

    #[test]
    fn test_block_header_metadata_size() {
        let block_header_metadata = BlockHeaderMetadata {
            timestamp: Utc::now().timestamp(),
            difficulty_target: 0u64,
            nonce: 0u32,
        };
        assert_eq!(
            block_header_metadata.to_bytes_le().unwrap().len(),
            BlockHeaderMetadata::size()
        );
    }
}
