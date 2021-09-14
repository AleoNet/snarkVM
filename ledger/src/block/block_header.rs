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
    posw::{txids_to_roots, PoswMarlin},
    BlockHeaderHash,
    BlockHeaderMetadata,
    MerkleRootHash,
    PedersenMerkleRootHash,
    ProofOfSuccinctWork,
    Transactions,
};
use snarkvm_algorithms::{crh::BHPCompressedCRH, traits::CRH};
use snarkvm_dpc::TransactionScheme;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};
use std::io::{Read, Result as IoResult, Write};

use snarkvm_curves::edwards_bls12::EdwardsProjective as EdwardsBls;

use once_cell::sync::Lazy;
use std::sync::Arc;

pub type BlockHeaderCRH = BHPCompressedCRH<EdwardsBls, 113, 63>;

/// Size of a block header in bytes - 887 bytes.
const HEADER_SIZE: usize = {
    BlockHeaderHash::size()
        + PedersenMerkleRootHash::size()
        + MerkleRootHash::size()
        + BlockHeaderMetadata::size()
        + ProofOfSuccinctWork::size()
};

/// Lazily evaluated BlockHeader CRH
pub static BLOCK_HEADER_CRH: Lazy<Arc<BlockHeaderCRH>> =
    Lazy::new(|| Arc::new(BlockHeaderCRH::setup("BlockHeaderCRH")));

/// Block header.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct BlockHeader {
    /// Hash of the previous block - 32 bytes
    pub previous_block_hash: BlockHeaderHash,
    /// Merkle root representing the transactions in the block - 32 bytes
    pub transactions_root: PedersenMerkleRootHash,
    /// The Merkle root representing the ledger commitments - 32 bytes
    pub commitments_root: MerkleRootHash,
    /// The block header metadata - 20 bytes
    pub metadata: BlockHeaderMetadata,
    /// Proof of Succinct Work
    pub proof: ProofOfSuccinctWork,
}

impl BlockHeader {
    /// Initializes a new instance of a block header.
    pub fn new<T: TransactionScheme, R: Rng + CryptoRng>(
        previous_block_hash: BlockHeaderHash,
        transactions: &Transactions<T>,
        commitments_root: MerkleRootHash,
        timestamp: i64,
        difficulty_target: u64,
        max_nonce: u32,
        rng: &mut R,
    ) -> Result<Self> {
        assert!(!(*transactions).is_empty(), "Cannot create block with no transactions");

        let txids = transactions.to_transaction_ids()?;
        let (_, transactions_root, subroots) = txids_to_roots(&txids);

        // TODO (howardwu): Make this a static once_cell.
        // Mine the block.
        let posw = PoswMarlin::load()?;
        let (nonce, proof) = posw.mine(&subroots, difficulty_target, rng, max_nonce)?;

        let metadata = BlockHeaderMetadata::new(timestamp, difficulty_target, nonce);

        Ok(Self {
            previous_block_hash,
            transactions_root,
            commitments_root,
            metadata,
            proof: proof.into(),
        })
    }

    /// Initializes a new instance of a genesis block header.
    pub fn new_genesis<T: TransactionScheme, R: Rng + CryptoRng>(
        transactions: &Transactions<T>,
        rng: &mut R,
    ) -> Result<Self> {
        let previous_block_hash = BlockHeaderHash([0u8; 32]);
        let commitments_root = MerkleRootHash([0u8; 32]);
        let timestamp = 0i64;
        let difficulty_target = u64::MAX;
        let max_nonce = u32::MAX;

        let block_header = Self::new(
            previous_block_hash,
            transactions,
            commitments_root,
            timestamp,
            difficulty_target,
            max_nonce,
            rng,
        )?;

        match block_header.is_genesis() {
            true => Ok(block_header),
            false => Err(anyhow!("Failed to initialize a genesis block header")),
        }
    }

    /// Returns `true` if the block header is a genesis block header.
    pub fn is_genesis(&self) -> bool {
        // Ensure the timestamp in the genesis block is 0.
        self.metadata.timestamp == 0
            // Ensure the previous block hash in the genesis block is 0.
            || self.previous_block_hash == BlockHeaderHash([0u8; 32])
    }

    pub fn to_hash(&self) -> Result<BlockHeaderHash> {
        let serialized = self.to_bytes_le()?;
        let hash_bytes = BLOCK_HEADER_CRH.hash(&serialized)?.to_bytes_le()?;

        let mut hash = [0u8; 32];
        hash.copy_from_slice(&hash_bytes);

        Ok(BlockHeaderHash(hash))
    }

    pub fn to_difficulty_target(&self) -> Result<u64> {
        let hash_slice = BLOCK_HEADER_CRH.hash(&self.proof.0[..])?.to_bytes_le()?;
        let mut hash = [0u8; 8];
        hash[..].copy_from_slice(&hash_slice[..8]);
        Ok(u64::from_le_bytes(hash))
    }

    pub const fn size() -> usize {
        HEADER_SIZE
    }
}

impl ToBytes for BlockHeader {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.previous_block_hash.0.write_le(&mut writer)?;
        self.transactions_root.0.write_le(&mut writer)?;
        self.commitments_root.0.write_le(&mut writer)?;
        self.metadata.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}

impl FromBytes for BlockHeader {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let previous_block_hash = <[u8; 32]>::read_le(&mut reader)?;
        let transactions_root = <[u8; 32]>::read_le(&mut reader)?;
        let commitments_root = <[u8; 32]>::read_le(&mut reader)?;
        let metadata = BlockHeaderMetadata::read_le(&mut reader)?;
        let proof = ProofOfSuccinctWork::read_le(&mut reader)?;

        Ok(Self {
            previous_block_hash: BlockHeaderHash(previous_block_hash),
            transactions_root: PedersenMerkleRootHash(transactions_root),
            commitments_root: MerkleRootHash(commitments_root),
            metadata,
            proof,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_dpc::{testnet2::Testnet2Parameters, Transaction};
    use snarkvm_parameters::{testnet2::Transaction1, Genesis};

    use chrono::Utc;
    use rand::thread_rng;

    #[test]
    fn test_block_header_genesis() {
        let block_header = BlockHeader::new_genesis(
            &Transactions::from(&[
                Transaction::<Testnet2Parameters>::from_bytes_le(&Transaction1::load_bytes()).unwrap(),
            ]),
            &mut thread_rng(),
        )
        .unwrap();
        assert!(block_header.is_genesis());

        // Ensure the genesis block contains the following.
        assert_eq!(block_header.previous_block_hash, BlockHeaderHash([0u8; 32]));
        assert_eq!(block_header.metadata.timestamp, 0);
        assert_eq!(block_header.metadata.difficulty_target, u64::MAX);

        // Ensure the genesis block does *not* contain the following.
        assert_ne!(block_header.transactions_root, PedersenMerkleRootHash([0u8; 32]));
        assert_ne!(block_header.commitments_root, MerkleRootHash([0u8; 32]));
        assert_ne!(
            block_header.proof,
            ProofOfSuccinctWork([0u8; ProofOfSuccinctWork::size()])
        );
    }

    #[test]
    fn test_block_header_serialization() {
        let block_header = BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            transactions_root: PedersenMerkleRootHash([0u8; 32]),
            commitments_root: MerkleRootHash([0u8; 32]),
            metadata: BlockHeaderMetadata::new(Utc::now().timestamp(), 0u64, 0u32),
            proof: ProofOfSuccinctWork([0u8; ProofOfSuccinctWork::size()]),
        };

        let serialized = block_header.to_bytes_le().unwrap();
        assert_eq!(&serialized[..], &bincode::serialize(&block_header).unwrap()[..]);

        let deserialized = BlockHeader::read_le(&serialized[..]).unwrap();
        assert_eq!(deserialized, block_header);
    }

    #[test]
    fn test_block_header_size() {
        let block_header = BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            transactions_root: PedersenMerkleRootHash([0u8; 32]),
            commitments_root: MerkleRootHash([0u8; 32]),
            metadata: BlockHeaderMetadata::new(Utc::now().timestamp(), 0u64, 0u32),
            proof: ProofOfSuccinctWork([0u8; ProofOfSuccinctWork::size()]),
        };
        assert_eq!(block_header.to_bytes_le().unwrap().len(), BlockHeader::size());
    }
}
