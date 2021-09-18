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
    /// The height of this block - 4 bytes.
    height: u32,
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
    pub fn new(height: u32, timestamp: i64, difficulty_target: u64, nonce: u32) -> Self {
        Self {
            height,
            timestamp,
            difficulty_target,
            nonce,
        }
    }

    /// Initializes a new instance of a genesis block header metadata.
    pub fn new_genesis() -> Self {
        let height = 0u32;
        let timestamp = 0i64;
        let difficulty_target = u64::MAX;
        let nonce = u32::MAX;

        Self::new(height, timestamp, difficulty_target, nonce)
    }

    /// Returns `true` if the block header metadata is for a genesis block header.
    pub fn is_genesis(&self) -> bool {
        // Ensure the height in the genesis block is 0.
        self.height == 0u32
            // Ensure the timestamp in the genesis block is 0.
            && self.timestamp == 0i64
            // Ensure the difficulty target in the genesis block is u64::MAX.
            && self.difficulty_target == u64::MAX
            // Ensure the nonce is u32::MAX.
            && self.nonce == u32::MAX
    }

    /// Returns `true` if the block header metadata is well-formed.
    pub fn is_valid(&self) -> bool {
        match self.height == 0u32 {
            true => self.is_genesis(),
            false => {
                // Ensure the timestamp in the block is not 0.
                self.timestamp != 0i64
            }
        }
    }

    /// Returns the block height.
    pub const fn height(&self) -> u32 {
        self.height
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
        size_of::<u32>() + size_of::<i64>() + size_of::<u64>() + size_of::<u32>()
    }
}

impl FromBytes for BlockHeaderMetadata {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let height = <[u8; 4]>::read_le(&mut reader)?;
        let timestamp = <[u8; 8]>::read_le(&mut reader)?;
        let difficulty_target = <[u8; 8]>::read_le(&mut reader)?;
        let nonce = <[u8; 4]>::read_le(&mut reader)?;

        Ok(Self {
            height: u32::from_le_bytes(height),
            timestamp: i64::from_le_bytes(timestamp),
            difficulty_target: u64::from_le_bytes(difficulty_target),
            nonce: u32::from_le_bytes(nonce),
        })
    }
}

impl ToBytes for BlockHeaderMetadata {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.height.to_le_bytes().write_le(&mut writer)?;
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
        let metadata = BlockHeaderMetadata::new(1, Utc::now().timestamp(), 2, 3);

        let serialized = metadata.to_bytes_le().unwrap();
        assert_eq!(&serialized[..], &bincode::serialize(&metadata).unwrap()[..]);

        let deserialized = BlockHeaderMetadata::read_le(&serialized[..]).unwrap();
        assert_eq!(deserialized, metadata);
    }

    #[test]
    fn test_block_header_metadata_size() {
        let metadata = BlockHeaderMetadata::new(1, Utc::now().timestamp(), 2, 3);
        assert_eq!(metadata.to_bytes_le().unwrap().len(), BlockHeaderMetadata::size());
    }
}
