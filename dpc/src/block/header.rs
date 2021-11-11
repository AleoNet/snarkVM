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

use crate::{BlockError, Network, PoSWScheme};
use snarkvm_algorithms::merkle_tree::{MerklePath, MerkleTree};
use snarkvm_utilities::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use serde::{
    de,
    ser::{Error, SerializeStruct},
    Deserialize,
    Deserializer,
    Serialize,
    Serializer,
};
use std::{
    mem::size_of,
    sync::{atomic::AtomicBool, Arc},
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockHeader<N: Network> {
    /// The Merkle root representing the blocks in the ledger up to the previous block - 32 bytes
    previous_ledger_root: N::LedgerRoot,
    /// The Merkle root representing the transactions in the block - 32 bytes
    transactions_root: N::TransactionsRoot,
    /// The block header metadata - 52 bytes
    metadata: BlockHeaderMetadata<N>,
    /// Proof of Succinct Work - 771 bytes
    proof: Option<N::PoSWProof>,
}

impl<N: Network> BlockHeader<N> {
    /// Initializes a new instance of a block header.
    pub fn mine<R: Rng + CryptoRng>(
        block_height: u32,
        block_timestamp: i64,
        difficulty_target: u64,
        previous_ledger_root: N::LedgerRoot,
        transactions_root: N::TransactionsRoot,
        terminator: &AtomicBool,
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
            previous_ledger_root,
            transactions_root,
            metadata,
            proof: None,
        };
        debug_assert!(!block_header.is_valid(), "Block header with a missing proof is invalid");

        // Mine the block.
        N::posw().mine(&mut block_header, terminator, rng)?;

        // Ensure the block header is valid.
        match block_header.is_valid() {
            true => Ok(block_header),
            false => Err(anyhow!("Failed to initialize a block header")),
        }
    }

    /// Returns `true` if the block header is well-formed.
    pub fn is_valid(&self) -> bool {
        println!("11");
        // Ensure the ledger root is nonzero.
        if self.previous_ledger_root == Default::default() {
            eprintln!("Invalid ledger root in block header");
            return false;
        }

        // Ensure the transactions root is nonzero.
        if self.transactions_root == Default::default() {
            eprintln!("Invalid transactions root in block header");
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

    /// Returns the previous ledger root from the block header.
    pub fn previous_ledger_root(&self) -> N::LedgerRoot {
        self.previous_ledger_root
    }

    /// Returns the transactions root in the block header.
    pub fn transactions_root(&self) -> N::TransactionsRoot {
        self.transactions_root
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
    pub fn proof(&self) -> &Option<N::PoSWProof> {
        &self.proof
    }

    /// Returns the block header size in bytes - 887 bytes.
    pub fn size() -> usize {
        32 // LedgerRoot
            + 32 // TransactionsRoot
            + BlockHeaderMetadata::<N>::size()
            + N::HEADER_PROOF_SIZE_IN_BYTES
    }

    /// Returns an instance of the block header tree.
    pub fn to_header_tree(&self) -> Result<MerkleTree<N::BlockHeaderRootParameters>> {
        let previous_ledger_root = self.previous_ledger_root.to_bytes_le()?;
        assert_eq!(previous_ledger_root.len(), 32);

        let transactions_root = self.transactions_root.to_bytes_le()?;
        assert_eq!(transactions_root.len(), 32);

        let metadata = self.metadata.to_bytes_le()?;
        assert_eq!(metadata.len(), 52);

        let num_leaves = usize::pow(2, N::HEADER_TREE_DEPTH as u32);
        let mut leaves: Vec<Vec<u8>> = Vec::with_capacity(num_leaves);
        leaves.push(previous_ledger_root);
        leaves.push(transactions_root);
        leaves.push(vec![0u8; 32]);
        leaves.push(metadata);
        // Sanity check that the correct number of leaves are allocated.
        assert_eq!(num_leaves, leaves.len());

        Ok(MerkleTree::<N::BlockHeaderRootParameters>::new(
            Arc::new(N::block_header_root_parameters().clone()),
            &leaves,
        )?)
    }

    /// Returns an instance of the block header tree.
    pub fn to_header_inclusion_proof(
        &self,
        index: usize,
        leaf: impl ToBytes,
    ) -> Result<MerklePath<N::BlockHeaderRootParameters>> {
        let leaf_bytes = leaf.to_bytes_le()?;
        assert_eq!(leaf_bytes.len(), 32);

        Ok(self.to_header_tree()?.generate_proof(index, &leaf_bytes)?)
    }

    /// Returns the block header root.
    pub fn to_header_root(&self) -> Result<N::BlockHeaderRoot> {
        Ok((*self.to_header_tree()?.root()).into())
    }

    /// Sets the block header nonce to the given nonce.
    /// This method is used by PoSW to iterate over candidate block headers.
    pub(crate) fn set_nonce(&mut self, nonce: N::InnerScalarField) {
        self.metadata.nonce = nonce;
    }

    /// Sets the block header proof to the given proof.
    /// This method is used by PoSW to iterate over candidate block headers.
    pub(crate) fn set_proof(&mut self, proof: N::PoSWProof) {
        self.proof = Some(proof);
    }
}

impl<N: Network> FromBytes for BlockHeader<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the header core variables.
        let previous_ledger_root = FromBytes::read_le(&mut reader)?;
        let transactions_root = FromBytes::read_le(&mut reader)?;

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
            previous_ledger_root,
            transactions_root,
            metadata,
            proof: Some(proof),
        };

        println!("aa");

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
        self.previous_ledger_root.write_le(&mut writer)?;
        self.transactions_root.write_le(&mut writer)?;

        // Write the header metadata.
        self.metadata.height.to_le_bytes().write_le(&mut writer)?;
        self.metadata.timestamp.to_le_bytes().write_le(&mut writer)?;
        self.metadata.difficulty_target.to_le_bytes().write_le(&mut writer)?;
        self.metadata.nonce.write_le(&mut writer)?;

        // Write the header proof.
        proof.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for BlockHeader<N> {
    type Err = anyhow::Error;

    fn from_str(header: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(&header)?)
    }
}

impl<N: Network> fmt::Display for BlockHeader<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            serde_json::to_string(self).map_err::<fmt::Error, _>(serde::ser::Error::custom)?
        )
    }
}

impl<N: Network> Serialize for BlockHeader<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut header = serializer.serialize_struct("BlockHeader", 4)?;
                header.serialize_field("previous_ledger_root", &self.previous_ledger_root)?;
                header.serialize_field("transactions_root", &self.transactions_root)?;
                header.serialize_field("metadata", &self.metadata)?;
                header.serialize_field("proof", &self.proof)?;
                header.end()
            }
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for BlockHeader<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let header = serde_json::Value::deserialize(deserializer)?;
                Ok(Self {
                    previous_ledger_root: serde_json::from_value(header["previous_ledger_root"].clone())
                        .map_err(de::Error::custom)?,
                    transactions_root: serde_json::from_value(header["transactions_root"].clone())
                        .map_err(de::Error::custom)?,
                    metadata: serde_json::from_value(header["metadata"].clone()).map_err(de::Error::custom)?,
                    proof: serde_json::from_value(header["proof"].clone()).map_err(de::Error::custom)?,
                })
            }
            false => FromBytesDeserializer::<Self>::deserialize(deserializer, "block header", Self::size()),
        }
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
    fn test_block_header_serde_json() {
        let block_header = Testnet2::genesis_block().header().to_owned();

        // Serialize
        let expected_string = block_header.to_string();
        let candidate_string = serde_json::to_string(&block_header).unwrap();
        assert_eq!(1593, candidate_string.len(), "Update me if serialization has changed");
        assert_eq!(expected_string, candidate_string);

        // Deserialize
        assert_eq!(block_header, BlockHeader::from_str(&candidate_string).unwrap());
        assert_eq!(block_header, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_block_header_bincode() {
        let block_header = Testnet2::genesis_block().header().to_owned();

        let expected_bytes = block_header.to_bytes_le().unwrap();
        assert_eq!(&expected_bytes[..], &bincode::serialize(&block_header).unwrap()[..]);

        assert_eq!(block_header, BlockHeader::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(block_header, bincode::deserialize(&expected_bytes[..]).unwrap());
    }

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
        assert_ne!(block_header.previous_ledger_root, Default::default());
        assert_ne!(block_header.transactions_root, Default::default());
    }

    #[test]
    fn test_block_header_difficulty_target() {
        // Construct an instance of PoSW.
        let posw = {
            let max_degree =
                AHPForR1CS::<<Testnet2 as Network>::InnerScalarField>::max_degree(20000, 20000, 200000).unwrap();
            let universal_srs =
                <<Testnet2 as Network>::PoSWSNARK as SNARK>::universal_setup(&max_degree, &mut thread_rng()).unwrap();
            <<Testnet2 as Network>::PoSW as PoSWScheme<Testnet2>>::setup::<ThreadRng>(
                &mut SRS::<ThreadRng, _>::Universal(&universal_srs),
            )
            .unwrap()
        };

        // Construct an assigned circuit.
        let mut block_header = Testnet2::genesis_block().header().clone();

        // Construct a PoSW proof.
        posw.mine(&mut block_header, &AtomicBool::new(false), &mut thread_rng())
            .unwrap();

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
    fn test_block_header_serialization_bincode() {
        let block_header = Testnet2::genesis_block().header().clone();

        println!("start");
        let serialized = &bincode::serialize(&block_header).unwrap();

        println!("start 1");

        let deserialized: BlockHeader<Testnet2> = bincode::deserialize(&serialized[..]).unwrap();

        println!("start 2");

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
