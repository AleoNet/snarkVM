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

use crate::{BlockHeader, BlockScheme, BlockTransactions, Network};
use snarkvm_algorithms::CRH;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use std::io::{Read, Result as IoResult, Write};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Block<N: Network> {
    /// Hash of the previous block - 32 bytes
    pub previous_hash: N::BlockHash,
    /// First `HEADER_SIZE` bytes of the block as defined by the encoding used by "block" messages.
    pub header: BlockHeader<N>,
    /// The block transactions.
    pub transactions: BlockTransactions<N>,
}

impl<N: Network> BlockScheme for Block<N> {
    type BlockHash = N::BlockHash;
    type Commitment = N::Commitment;
    type Header = BlockHeader<N>;
    type SerialNumber = N::SerialNumber;
    type Transactions = BlockTransactions<N>;

    /// Returns `true` if the block is well-formed.
    fn is_valid(&self) -> bool {
        // Ensure the previous block hash is well-formed.
        if self.header.height() == 0u32 {
            if self.previous_hash != Default::default() {
                eprintln!("Genesis block must have an empty previous block hash");
                return false;
            }
        } else {
            if self.previous_hash == Default::default() {
                eprintln!("Block must have a non-empty previous block hash");
                return false;
            }
        }

        self.header.is_valid() && self.transactions.is_valid()
    }

    /// Returns the previous block hash.
    fn previous_hash(&self) -> &Self::BlockHash {
        &self.previous_hash
    }

    /// Returns the header.
    fn header(&self) -> &Self::Header {
        &self.header
    }

    /// Returns the transactions.
    fn transactions(&self) -> &Self::Transactions {
        &self.transactions
    }

    /// Returns the block height.
    fn height(&self) -> u32 {
        self.header.height()
    }

    /// Returns the hash of this block.
    fn to_block_hash(&self) -> Result<Self::BlockHash> {
        // Construct the preimage.
        let mut preimage = self.previous_hash.to_bytes_le()?;
        preimage.extend_from_slice(&self.header.to_root()?.to_bytes_le()?);

        Ok(N::block_hash_crh().hash(&preimage)?)
    }

    /// Returns the commitments in the block, by constructing a flattened list of commitments from all transactions.
    fn to_commitments(&self) -> Result<Vec<Self::Commitment>> {
        self.transactions.to_commitments()
    }

    /// Returns the serial numbers in the block, by constructing a flattened list of serial numbers from all transactions.
    fn to_serial_numbers(&self) -> Result<Vec<Self::SerialNumber>> {
        self.transactions.to_serial_numbers()
    }
}

impl<N: Network> FromBytes for Block<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let previous_hash = FromBytes::read_le(&mut reader)?;
        let header = FromBytes::read_le(&mut reader)?;
        let transactions = FromBytes::read_le(&mut reader)?;

        Ok(Self {
            previous_hash,
            header,
            transactions,
        })
    }
}

impl<N: Network> ToBytes for Block<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.previous_hash.write_le(&mut writer)?;
        self.header.write_le(&mut writer)?;
        self.transactions.write_le(&mut writer)
    }
}
