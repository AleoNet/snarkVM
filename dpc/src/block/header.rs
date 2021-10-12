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

use crate::{BlockError, Network, PoSWScheme, ProofOfSuccinctWork};
use snarkvm_algorithms::merkle_tree::{MerklePath, MerkleTree};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use serde::{ser::Error, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    io::{Read, Result as IoResult, Write},
    mem::size_of,
    sync::Arc,
};

pub mod proof_serialization {
    use super::*;
    pub fn serialize<S: Serializer, T: Serialize>(proof: &Option<T>, s: S) -> Result<S::Ok, S::Error> {
        match *proof {
            Some(ref d) => d.serialize(s),
            None => Err(S::Error::custom("Proof must be set to serialize block header")),
        }
    }
    pub fn deserialize<'de, D: Deserializer<'de>, T: Deserialize<'de>>(deserializer: D) -> Result<Option<T>, D::Error> {
        Ok(T::deserialize(deserializer).ok())
    }
}

/// Block header metadata.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct BlockHeaderMetadata<N: Network> {
    /// The height of this block - 4 bytes.
    height: u32,
    /// The block timestamp is a Unix epoch time (UTC) (according to the miner) - 8 bytes
    timestamp: i64,
    /// Proof of work algorithm difficulty target for this block - 8 bytes
    difficulty_target: u64,
    /// Nonce for solving the PoW puzzle - 32 bytes
    nonce: N::InnerScalarField,
}

impl<N: Network> BlockHeaderMetadata<N> {
    /// Initializes a new instance of a genesis block header metadata.
    pub fn genesis() -> Self {
        Self {
            height: 0u32,
            timestamp: 0i64,
            difficulty_target: u64::MAX,
            nonce: Default::default(),
        }
    }

    /// Returns the size (in bytes) of a block header's metadata.
    pub fn size() -> usize {
        size_of::<u32>() + size_of::<i64>() + size_of::<u64>() + 32 // N::InnerScalarField
    }
}

impl<N: Network> ToBytes for BlockHeaderMetadata<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.height.to_le_bytes().write_le(&mut writer)?;
        self.timestamp.to_le_bytes().write_le(&mut writer)?;
        self.difficulty_target.to_le_bytes().write_le(&mut writer)?;
        self.nonce.write_le(&mut writer)
    }
}

/// Block header.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockHeader<N: Network> {
    /// The Merkle root representing the transactions in the block - 32 bytes
    transactions_root: N::TransactionsRoot,
    /// The Merkle root representing the ledger serial numbers - 32 bytes
    serial_numbers_root: N::SerialNumbersRoot,
    /// The Merkle root representing the ledger commitments - 32 bytes
    commitments_root: N::CommitmentsRoot,
    /// The block header metadata - 52 bytes
    metadata: BlockHeaderMetadata<N>,
    /// Proof of Succinct Work - 771 bytes
    #[serde(with = "proof_serialization")]
    proof: Option<ProofOfSuccinctWork<N>>,
}

impl<N: Network> BlockHeader<N> {
    /// Initializes a new instance of a block header.
    pub fn new<R: Rng + CryptoRng>(
        block_height: u32,
        block_timestamp: i64,
        difficulty_target: u64,
        transactions_root: N::TransactionsRoot,
        serial_numbers_root: N::SerialNumbersRoot,
        commitments_root: N::CommitmentsRoot,
        rng: &mut R,
    ) -> Result<Self> {
        // Construct the candidate block metadata.
        let metadata = match block_height == 0 {
            true => BlockHeaderMetadata::genesis(),
            false => BlockHeaderMetadata {
                height: block_height,
                timestamp: block_timestamp,
                difficulty_target,
                nonce: Default::default(),
            },
        };

        // Construct a candidate block header.
        let mut block_header = Self {
            transactions_root,
            serial_numbers_root,
            commitments_root,
            metadata,
            proof: None,
        };
        debug_assert!(!block_header.is_valid(), "Block header with a missing proof is invalid");

        // Mine the block.
        N::posw().mine(&mut block_header, rng)?;

        // Ensure the block header is valid.
        match block_header.is_valid() {
            true => Ok(block_header),
            false => Err(anyhow!("Failed to initialize a block header")),
        }
    }

    /// Returns `true` if the block header is well-formed.
    pub fn is_valid(&self) -> bool {
        // Ensure the transactions root is nonzero.
        if self.transactions_root == Default::default() {
            eprintln!("Invalid transactions root in block header");
            return false;
        }

        // Ensure the serial numbers root is nonzero.
        if self.serial_numbers_root == Default::default() {
            eprintln!("Invalid serial numbers root in block header");
            return false;
        }

        // Ensure the commitments root is nonzero.
        if self.commitments_root == Default::default() {
            eprintln!("Invalid commitments root in block header");
            return false;
        }

        // Ensure the metadata and proof are valid.
        match self.metadata.height == 0u32 {
            true => self.is_genesis(),
            false => {
                // TODO (howardwu): CRITICAL - Fill in after refactor is complete.
                // Ensure the timestamp in the block is greater than 0.
                self.metadata.timestamp > 0i64
                    // Ensure the PoSW proof is valid.
                    && N::posw().verify(&self)
            }
        }
    }

    /// Returns `true` if the block header is a genesis block header.
    pub fn is_genesis(&self) -> bool {
        // Ensure the height in the genesis block is 0.
        self.metadata.height == 0u32
            // Ensure the timestamp in the genesis block is 0.
            && self.metadata.timestamp == 0i64
            // Ensure the difficulty target in the genesis block is u64::MAX.
            && self.metadata.difficulty_target == u64::MAX
            // Ensure the PoSW proof is valid.
            && N::posw().verify(&self)
    }

    /// Returns the transactions root in the block header.
    pub fn transactions_root(&self) -> N::TransactionsRoot {
        self.transactions_root
    }

    /// Returns the serial numbers root in the block header.
    pub fn serial_numbers_root(&self) -> N::SerialNumbersRoot {
        self.serial_numbers_root
    }

    /// Returns the commitments root in the block header.
    pub fn commitments_root(&self) -> N::CommitmentsRoot {
        self.commitments_root
    }

    /// Returns the block height.
    pub fn height(&self) -> u32 {
        self.metadata.height
    }

    /// Returns the block timestamp.
    pub fn timestamp(&self) -> i64 {
        self.metadata.timestamp
    }

    /// Returns the block difficulty target.
    pub fn difficulty_target(&self) -> u64 {
        self.metadata.difficulty_target
    }

    /// Returns the block nonce.
    pub fn nonce(&self) -> N::InnerScalarField {
        self.metadata.nonce
    }

    /// Returns the proof, if it is set.
    pub fn proof(&self) -> &Option<ProofOfSuccinctWork<N>> {
        &self.proof
    }

    /// Returns the block header size in bytes - 919 bytes.
    pub fn size() -> usize {
        32 // TransactionsRoot
            + 32 // SerialNumbersRoot
            + 32 // CommitmentsRoot
            + BlockHeaderMetadata::<N>::size()
            + N::POSW_PROOF_SIZE_IN_BYTES
    }

    /// Returns an instance of the block header tree.
    pub fn to_header_tree(&self) -> Result<MerkleTree<N::BlockHeaderTreeParameters>> {
        let transactions_root = self.transactions_root.to_bytes_le()?;
        assert_eq!(transactions_root.len(), 32);

        let serial_numbers_root = self.serial_numbers_root.to_bytes_le()?;
        assert_eq!(serial_numbers_root.len(), 32);

        let commitments_root = self.commitments_root.to_bytes_le()?;
        assert_eq!(commitments_root.len(), 32);

        let metadata = self.metadata.to_bytes_le()?;
        assert_eq!(metadata.len(), 52);

        let mut leaves: Vec<Vec<u8>> = Vec::with_capacity(N::POSW_NUM_LEAVES);
        leaves.push(transactions_root);
        leaves.push(serial_numbers_root);
        leaves.push(commitments_root);
        leaves.push(vec![0u8; 32]);
        leaves.push(vec![0u8; 32]);
        leaves.push(vec![0u8; 32]);
        leaves.push(vec![0u8; 32]);
        leaves.push(metadata);
        assert_eq!(N::POSW_NUM_LEAVES, leaves.len());

        Ok(MerkleTree::<N::BlockHeaderTreeParameters>::new(
            Arc::new(N::block_header_tree_parameters().clone()),
            &leaves,
        )?)
    }

    /// Returns an instance of the block header tree.
    pub fn to_header_inclusion_proof(
        &self,
        index: usize,
        leaf: impl ToBytes,
    ) -> Result<MerklePath<N::BlockHeaderTreeParameters>> {
        let leaf_bytes = leaf.to_bytes_le()?;
        assert_eq!(leaf_bytes.len(), 32);

        Ok(self.to_header_tree()?.generate_proof(index, &leaf_bytes)?)
    }

    /// Returns the block header root.
    pub fn to_header_root(&self) -> Result<N::BlockHeaderRoot> {
        Ok(*self.to_header_tree()?.root())
    }

    /// Sets the block header nonce to the given nonce.
    /// This method is used by PoSW to iterate over candidate block headers.
    pub(crate) fn set_nonce(&mut self, nonce: N::InnerScalarField) {
        self.metadata.nonce = nonce;
    }

    /// Sets the block header proof to the given proof.
    /// This method is used by PoSW to iterate over candidate block headers.
    pub(crate) fn set_proof(&mut self, proof: ProofOfSuccinctWork<N>) {
        self.proof = Some(proof);
    }
}

impl<N: Network> FromBytes for BlockHeader<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the header core variables.
        let transactions_root = FromBytes::read_le(&mut reader)?;
        let serial_numbers_root = FromBytes::read_le(&mut reader)?;
        let commitments_root = FromBytes::read_le(&mut reader)?;

        // Read the header metadata.
        let height = <[u8; 4]>::read_le(&mut reader)?;
        let timestamp = <[u8; 8]>::read_le(&mut reader)?;
        let difficulty_target = <[u8; 8]>::read_le(&mut reader)?;
        let nonce = FromBytes::read_le(&mut reader)?;

        let metadata = BlockHeaderMetadata {
            height: u32::from_le_bytes(height),
            timestamp: i64::from_le_bytes(timestamp),
            difficulty_target: u64::from_le_bytes(difficulty_target),
            nonce,
        };

        // Read the header proof.
        let proof = FromBytes::read_le(&mut reader)?;

        // Construct the block header.
        let block_header = Self {
            transactions_root,
            serial_numbers_root,
            commitments_root,
            metadata,
            proof: Some(proof),
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
        // In this context, proof must always be set.
        let proof = match &self.proof {
            Some(proof) => proof,
            None => return Err(BlockError::Message("Proof must be set to serialize block header".to_string()).into()),
        };

        // Write the header core variables.
        self.transactions_root.write_le(&mut writer)?;
        self.serial_numbers_root.write_le(&mut writer)?;
        self.commitments_root.write_le(&mut writer)?;

        // Write the header metadata.
        self.metadata.height.to_le_bytes().write_le(&mut writer)?;
        self.metadata.timestamp.to_le_bytes().write_le(&mut writer)?;
        self.metadata.difficulty_target.to_le_bytes().write_le(&mut writer)?;
        self.metadata.nonce.write_le(&mut writer)?;

        // Write the header proof.
        proof.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet2::Testnet2, PoSWScheme};
    use snarkvm_algorithms::{SNARK, SRS};
    use snarkvm_marlin::ahp::AHPForR1CS;

    use rand::{rngs::ThreadRng, thread_rng};

    #[test]
    fn test_block_header_genesis() {
        let block_header = Testnet2::genesis_block().header();
        assert!(block_header.is_genesis());

        // Ensure the genesis block contains the following.
        assert_eq!(block_header.metadata.height, 0);
        assert_eq!(block_header.metadata.timestamp, 0);
        assert_eq!(block_header.metadata.difficulty_target, u64::MAX);
        assert!(block_header.proof.is_some());

        // Ensure the genesis block does *not* contain the following.
        assert_ne!(block_header.transactions_root, Default::default());
        assert_ne!(block_header.serial_numbers_root, Default::default());
        assert_ne!(block_header.commitments_root, Default::default());
    }

    #[test]
    fn test_block_header_difficulty_target() {
        // Construct an instance of PoSW.
        let posw = {
            let max_degree =
                AHPForR1CS::<<Testnet2 as Network>::InnerScalarField>::max_degree(20000, 20000, 200000).unwrap();
            let universal_srs =
                <<Testnet2 as Network>::PoswSNARK as SNARK>::universal_setup(&max_degree, &mut thread_rng()).unwrap();
            <<Testnet2 as Network>::PoSW as PoSWScheme<Testnet2>>::setup::<ThreadRng>(
                &mut SRS::<ThreadRng, _>::Universal(&universal_srs),
            )
            .unwrap()
        };

        // Construct an assigned circuit.
        let mut block_header = Testnet2::genesis_block().header().clone();

        // Construct a PoSW proof.
        posw.mine(&mut block_header, &mut thread_rng()).unwrap();

        // Check that the difficulty target is satisfied.
        assert!(posw.verify(&block_header));

        // Check that the difficulty target is *not* satisfied.
        block_header.metadata.difficulty_target = 0u64;
        assert!(!posw.verify(&block_header));
    }

    #[test]
    fn test_block_header_serialization() {
        let block_header = Testnet2::genesis_block().header().clone();

        let serialized = block_header.to_bytes_le().unwrap();
        assert_eq!(&serialized[..], &bincode::serialize(&block_header).unwrap()[..]);

        let deserialized = BlockHeader::read_le(&serialized[..]).unwrap();
        assert_eq!(deserialized, block_header);
    }

    #[test]
    fn test_block_header_size() {
        let block_header = Testnet2::genesis_block().header();

        assert_eq!(
            block_header.to_bytes_le().unwrap().len(),
            BlockHeader::<Testnet2>::size()
        );
        assert_eq!(
            bincode::serialize(&block_header).unwrap().len(),
            BlockHeader::<Testnet2>::size()
        );
    }
}
