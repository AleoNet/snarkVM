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

use crate::{
    posw::PoswMarlin,
    BlockHash,
    BlockHeader,
    BlockHeaderMetadata,
    BlockScheme,
    MerkleRoot,
    Network,
    ProofOfSuccinctWork,
    Transactions,
};
use snarkvm_algorithms::CRH;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::io::{Read, Result as IoResult, Write};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Block<N: Network> {
    /// Hash of the previous block - 32 bytes
    pub previous_block_hash: BlockHash,
    /// First `HEADER_SIZE` bytes of the block as defined by the encoding used by "block" messages.
    pub header: BlockHeader<N>,
    /// The block transactions.
    pub transactions: Transactions<N>,
    /// Proof of Succinct Work
    pub proof: ProofOfSuccinctWork<N>,
}

impl<N: Network> BlockScheme for Block<N> {
    type BlockHash = BlockHash;
    type BlockHeader = BlockHeader<N>;
    type CommitmentsRoot = N::CommitmentsRoot;
    type Proof = ProofOfSuccinctWork<N>;
    type Transactions = Transactions<N>;

    /// Initializes a new instance of a block.
    fn new<R: Rng + CryptoRng>(
        previous_block_hash: BlockHash,
        transactions: &Self::Transactions,
        commitments_root: Self::CommitmentsRoot,
        serial_numbers_root: MerkleRoot,
        block_height: u32,
        difficulty_target: u64,
        rng: &mut R,
    ) -> Result<Self> {
        assert!(!(*transactions).is_empty(), "Cannot create block with no transactions");

        // Construct a candidate block header.
        let metadata = BlockHeaderMetadata::new(block_height, difficulty_target);
        let mut header = BlockHeader::new(transactions, commitments_root, serial_numbers_root, metadata)?;

        // TODO (howardwu): TEMPORARY - Make this a static once_cell.
        // Mine the block.
        let posw = PoswMarlin::<N>::load(true)?;
        let proof = posw.mine(&mut header, rng)?;

        // Ensure the block header is valid.
        if !header.is_valid() {
            return Err(anyhow!("Invalid block header"));
        }

        // Serialize the proof.
        let proof = ProofOfSuccinctWork::new(&proof.to_bytes_le()?[..]);

        Ok(Self {
            previous_block_hash,
            header,
            transactions: transactions.clone(),
            proof,
        })
    }

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

    /// Returns the proof.
    fn proof(&self) -> &Self::Proof {
        &self.proof
    }

    /// Returns the hash of this block.
    fn to_hash(&self) -> Result<BlockHash> {
        // Construct the preimage.
        let mut preimage = self.previous_block_hash.0.to_vec();
        preimage.extend_from_slice(&self.header.to_root()?.to_bytes_le()?);

        let mut hash = [0u8; 32];
        hash.copy_from_slice(&N::block_hash_crh().hash(&preimage)?.to_bytes_le()?);

        Ok(BlockHash(hash))
    }
}

impl<N: Network> FromBytes for Block<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let previous_block_hash = FromBytes::read_le(&mut reader)?;
        let header = FromBytes::read_le(&mut reader)?;
        let transactions = FromBytes::read_le(&mut reader)?;
        let proof = ProofOfSuccinctWork::read_le(&mut reader)?;

        Ok(Self {
            previous_block_hash,
            header,
            transactions,
            proof,
        })
    }
}

impl<N: Network> ToBytes for Block<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.previous_block_hash.write_le(&mut writer)?;
        self.header.write_le(&mut writer)?;
        self.transactions.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}
