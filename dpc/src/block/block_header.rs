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
    BlockError,
    BlockHeaderMetadata,
    MerkleRoot,
    Network,
    ProofOfSuccinctWork,
    Transactions,
};
use snarkvm_algorithms::{merkle_tree::MerkleTree, CRH};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};
use std::{
    io::{Read, Result as IoResult, Write},
    sync::Arc,
};

/// Block header.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct BlockHeader<N: Network> {
    /// The Merkle root representing the transactions in the block - 32 bytes
    pub transactions_root: MerkleRoot,
    /// The Merkle root representing the ledger commitments - 32 bytes
    pub commitments_root: MerkleRoot,
    /// The Merkle root representing the ledger serial numbers - 32 bytes
    pub serial_numbers_root: MerkleRoot,
    /// The block header metadata - 24 bytes
    pub metadata: BlockHeaderMetadata,
    /// Proof of Succinct Work
    pub proof: ProofOfSuccinctWork<N>,
}

impl<N: Network> BlockHeader<N> {
    /// Initializes a new instance of a block header.
    pub fn new<R: Rng + CryptoRng>(
        transactions: &Transactions<N>,
        commitments_root: MerkleRoot,
        serial_numbers_root: MerkleRoot,
        block_height: u32,
        difficulty_target: u64,
        rng: &mut R,
    ) -> Result<Self> {
        assert!(!(*transactions).is_empty(), "Cannot create block with no transactions");

        let transactions_root = transactions.to_transactions_root()?;

        let mut posw_leaves: Vec<[u8; 32]> = Vec::with_capacity(4);
        posw_leaves.push(transactions_root.0);
        posw_leaves.push(commitments_root.0);
        posw_leaves.push(serial_numbers_root.0);
        posw_leaves.push([0u8; 32]);

        // TODO (howardwu): TEMPORARY - Make this a static once_cell.
        // Mine the block.
        let max_nonce = u32::MAX;
        let posw = PoswMarlin::<N>::load(true)?;
        let (nonce, proof) = posw.mine(&posw_leaves, difficulty_target, rng, max_nonce)?;

        // Construct the block header metadata.
        let metadata = BlockHeaderMetadata::new(block_height, difficulty_target, nonce);
        if !metadata.is_valid() {
            return Err(anyhow!("Invalid block header metadata"));
        }

        // Serialize the proof.
        let proof = ProofOfSuccinctWork::new(&proof.to_bytes_le()?[..]);

        Ok(Self {
            transactions_root,
            commitments_root,
            serial_numbers_root,
            metadata,
            proof,
        })
    }

    /// Initializes a new instance of a genesis block header.
    pub fn new_genesis<R: Rng + CryptoRng>(transactions: &Transactions<N>, rng: &mut R) -> Result<Self> {
        // Compute the commitments root from the transactions.
        let commitments = transactions.to_commitments()?;
        let commitments_tree = MerkleTree::new(Arc::new(N::commitments_tree_parameters().clone()), &commitments)?;
        let commitments_root = MerkleRoot::from_element(commitments_tree.root());

        // Compute the serial numbers root from the transactions.
        let serial_numbers = transactions.to_serial_numbers()?;
        let serial_numbers_tree =
            MerkleTree::new(Arc::new(N::serial_numbers_tree_parameters().clone()), &serial_numbers)?;
        let serial_numbers_root = MerkleRoot::from_element(serial_numbers_tree.root());

        // Compute the genesis block header.
        let height = 0u32;
        let difficulty_target = u64::MAX;
        let block_header = Self::new(
            transactions,
            commitments_root,
            serial_numbers_root,
            height,
            difficulty_target,
            rng,
        )?;

        match block_header.is_genesis() {
            true => Ok(block_header),
            false => Err(anyhow!("Failed to initialize a genesis block header")),
        }
    }

    /// Returns `true` if the block header is a genesis block header.
    pub fn is_genesis(&self) -> bool {
        // Ensure the metadata is for the genesis block.
        self.metadata.is_genesis()
    }

    /// Returns `true` if the block header is well-formed.
    pub fn is_valid(&self) -> bool {
        match self.metadata.height() == 0u32 {
            true => self.is_genesis(),
            false => {
                // TODO (howardwu): CRITICAL - Fill in after refactor is complete.
                self.metadata.is_valid()
            }
        }
    }

    /// Returns the block height.
    pub fn height(&self) -> u32 {
        self.metadata.height()
    }

    /// Returns the block timestamp.
    pub fn timestamp(&self) -> i64 {
        self.metadata.timestamp()
    }

    /// Returns the block difficulty target.
    pub fn difficulty_target(&self) -> u64 {
        self.metadata.difficulty_target()
    }

    /// Returns the block nonce.
    pub fn nonce(&self) -> u32 {
        self.metadata.nonce()
    }

    /// TODO (howardwu): CRITICAL - Implement a (masked) Merkle tree for the block header.
    pub fn to_root(&self) -> Result<N::BlockHeaderRoot> {
        Ok(N::block_header_tree_crh().hash(&self.to_bytes_le()?)?)
    }

    /// Returns the block header size in bytes - 891 bytes.
    pub fn size() -> usize {
        MerkleRoot::size()
            + MerkleRoot::size()
            + MerkleRoot::size()
            + BlockHeaderMetadata::size()
            + ProofOfSuccinctWork::<N>::size()
    }
}

impl<N: Network> FromBytes for BlockHeader<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let transactions_root = <[u8; 32]>::read_le(&mut reader)?;
        let commitments_root = <[u8; 32]>::read_le(&mut reader)?;
        let serial_numbers_root = <[u8; 32]>::read_le(&mut reader)?;
        let metadata = BlockHeaderMetadata::read_le(&mut reader)?;
        let proof = ProofOfSuccinctWork::read_le(&mut reader)?;

        let block_header = Self {
            transactions_root: MerkleRoot(transactions_root),
            commitments_root: MerkleRoot(commitments_root),
            serial_numbers_root: MerkleRoot(serial_numbers_root),
            metadata,
            proof,
        };

        // Ensure the block header is well-formed.
        match block_header.is_valid() {
            true => Ok(block_header),
            false => Err(BlockError::Message("Invalid block header".to_string()).into()),
        }
    }
}

impl<N: Network> ToBytes for BlockHeader<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.transactions_root.0.write_le(&mut writer)?;
        self.commitments_root.0.write_le(&mut writer)?;
        self.serial_numbers_root.0.write_le(&mut writer)?;
        self.metadata.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet2::Testnet2, Transaction};
    use snarkvm_parameters::{testnet2::Transaction1, Genesis};

    use rand::thread_rng;

    #[test]
    fn test_block_header_genesis() {
        let block_header = BlockHeader::<Testnet2>::new_genesis(
            &Transactions::from(&[Transaction::<Testnet2>::from_bytes_le(&Transaction1::load_bytes()).unwrap()]),
            &mut thread_rng(),
        )
        .unwrap();
        assert!(block_header.is_genesis());

        // Ensure the genesis block contains the following.
        assert_eq!(block_header.metadata.height(), 0);
        assert_eq!(block_header.metadata.timestamp(), 0);
        assert_eq!(block_header.metadata.difficulty_target(), u64::MAX);
        assert_eq!(block_header.metadata.nonce(), u32::MAX);

        // Ensure the genesis block does *not* contain the following.
        assert_ne!(block_header.transactions_root, MerkleRoot([0u8; 32]));
        assert_ne!(block_header.commitments_root, MerkleRoot([0u8; 32]));
        assert_ne!(block_header.serial_numbers_root, MerkleRoot([0u8; 32]));
        assert_ne!(
            block_header.proof,
            ProofOfSuccinctWork::new(&vec![0u8; ProofOfSuccinctWork::<Testnet2>::size()]),
        );
    }

    #[test]
    fn test_block_header_serialization() {
        let block_header = BlockHeader::<Testnet2> {
            transactions_root: MerkleRoot([0u8; 32]),
            commitments_root: MerkleRoot([0u8; 32]),
            serial_numbers_root: MerkleRoot([0u8; 32]),
            metadata: BlockHeaderMetadata::new_genesis(0),
            proof: ProofOfSuccinctWork::new(&vec![0u8; ProofOfSuccinctWork::<Testnet2>::size()]),
        };

        let serialized = block_header.to_bytes_le().unwrap();
        assert_eq!(&serialized[..], &bincode::serialize(&block_header).unwrap()[..]);

        let deserialized = BlockHeader::read_le(&serialized[..]).unwrap();
        assert_eq!(deserialized, block_header);
    }

    #[test]
    fn test_block_header_size() {
        let block_header = BlockHeader::<Testnet2> {
            transactions_root: MerkleRoot([0u8; 32]),
            commitments_root: MerkleRoot([0u8; 32]),
            serial_numbers_root: MerkleRoot([0u8; 32]),
            metadata: BlockHeaderMetadata::new_genesis(0),
            proof: ProofOfSuccinctWork::new(&vec![0u8; ProofOfSuccinctWork::<Testnet2>::size()]),
        };
        assert_eq!(
            block_header.to_bytes_le().unwrap().len(),
            BlockHeader::<Testnet2>::size()
        );
    }
}
