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

use crate::{BlockHash, BlockHeader, BlockScheme, Network, Transactions};
use snarkvm_algorithms::CRH;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use std::io::{Read, Result as IoResult, Write};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Block<N: Network> {
    /// Hash of the previous block - 32 bytes
    pub previous_block_hash: BlockHash,
    /// First `HEADER_SIZE` bytes of the block as defined by the encoding used by "block" messages.
    pub header: BlockHeader<N>,
    /// The block transactions.
    pub transactions: Transactions<N>,
}

impl<N: Network> BlockScheme for Block<N> {
    type BlockHash = BlockHash;
    type BlockHeader = BlockHeader<N>;
    type Transactions = Transactions<N>;

    /// Returns the previous block hash.
    fn previous_block_hash(&self) -> &Self::BlockHash {
        &self.previous_block_hash
    }

    /// Returns the header.
    fn header(&self) -> &Self::BlockHeader {
        &self.header
    }

    /// Returns the transactions.
    fn transactions(&self) -> &Self::Transactions {
        &self.transactions
    }

    /// Returns the hash of this block.
    fn to_hash(&self) -> Result<BlockHash> {
        // Construct the preimage.
        let mut preimage = self.previous_block_hash.0.to_vec();
        preimage.extend_from_slice(&self.header.to_hash()?.0);

        let mut hash = [0u8; 32];
        hash.copy_from_slice(&N::block_hash_crh().hash(&preimage)?.to_bytes_le()?);

        Ok(BlockHash(hash))
    }
}

impl<N: Network> FromBytes for Block<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let previous_block_hash: BlockHash = FromBytes::read_le(&mut reader)?;
        let header: BlockHeader<N> = FromBytes::read_le(&mut reader)?;
        let transactions: Transactions<N> = FromBytes::read_le(&mut reader)?;

        Ok(Self {
            previous_block_hash,
            header,
            transactions,
        })
    }
}

impl<N: Network> ToBytes for Block<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.previous_block_hash.write_le(&mut writer)?;
        self.header.write_le(&mut writer)?;
        self.transactions.write_le(&mut writer)
    }
}
