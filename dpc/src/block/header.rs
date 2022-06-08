// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::{BlockError, BlockTemplate, Network, PoSWCircuit, PoSWProof, PoSWScheme};
use snarkvm_algorithms::merkle_tree::{MerklePath, MerkleTree};
use snarkvm_utilities::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
    Uniform,
};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use serde::{de, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};
use std::{mem::size_of, sync::atomic::AtomicBool};

/// Block header metadata.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct BlockHeaderMetadata {
    /// The height of this block - 4 bytes.
    height: u32,
    /// The block timestamp is a Unix epoch time (UTC) (according to the miner) - 8 bytes
    timestamp: i64,
    /// The difficulty target for this block - 8 bytes
    difficulty_target: u64,
    /// The cumulative weight up to this block (inclusive) - 16 bytes
    cumulative_weight: u128,
}

impl BlockHeaderMetadata {
    /// Initializes a new instance of a block header metadata.
    pub fn new<N: Network>(template: &BlockTemplate<N>) -> Self {
        match template.block_height() == 0 {
            true => Self::genesis(),
            false => Self {
                height: template.block_height(),
                timestamp: template.block_timestamp(),
                difficulty_target: template.difficulty_target(),
                cumulative_weight: template.cumulative_weight(),
            },
        }
    }

    /// Initializes a new instance of a genesis block header metadata.
    pub fn genesis() -> Self {
        Self { height: 0u32, timestamp: 0i64, difficulty_target: u64::MAX, cumulative_weight: 0u128 }
    }

    /// Returns the size (in bytes) of a block header's metadata.
    pub fn size() -> usize {
        size_of::<u32>() + size_of::<i64>() + size_of::<u64>() + size_of::<u128>()
    }
}

impl ToBytes for BlockHeaderMetadata {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.height.to_le_bytes().write_le(&mut writer)?;
        self.timestamp.to_le_bytes().write_le(&mut writer)?;
        self.difficulty_target.to_le_bytes().write_le(&mut writer)?;
        self.cumulative_weight.to_le_bytes().write_le(&mut writer)
    }
}

/// Block header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockHeader<N: Network> {
    /// The Merkle root representing the blocks in the ledger up to the previous block
    previous_ledger_root: N::LedgerRoot,
    /// The Merkle root representing the transactions in the block
    transactions_root: N::TransactionsRoot,
    /// The block header metadata
    metadata: BlockHeaderMetadata,
    /// Nonce for Proof of Succinct Work
    nonce: N::PoSWNonce,
    /// Proof of Succinct Work
    proof: PoSWProof<N>,
}

impl<N: Network> BlockHeader<N> {
    /// Initializes a new instance of a block header.
    pub fn from(
        previous_ledger_root: N::LedgerRoot,
        transactions_root: N::TransactionsRoot,
        metadata: BlockHeaderMetadata,
        nonce: N::PoSWNonce,
        proof: PoSWProof<N>,
    ) -> Result<Self, BlockError> {
        // Construct the block header.
        let block_header = Self { previous_ledger_root, transactions_root, metadata, nonce, proof };

        // Ensure the block header is well-formed.
        match block_header.is_valid() {
            true => Ok(block_header),
            false => Err(BlockError::Message("Invalid block header".to_string())),
        }
    }

    /// Mines a new instance of a block header.
    pub fn mine<R: Rng + CryptoRng>(
        block_template: &BlockTemplate<N>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<Self> {
        // Mine the block.
        let block_header = N::posw().mine(block_template, terminator, rng)?;

        // Ensure the block header is valid.
        match block_header.is_valid() {
            true => Ok(block_header),
            false => Err(anyhow!("Failed to initialize a block header")),
        }
    }

    ///
    /// Mines a new unchecked instance of a block header.
    /// WARNING - This method does *not* enforce the block header is valid.
    ///
    pub fn mine_once_unchecked<R: Rng + CryptoRng>(
        block_template: &BlockTemplate<N>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<Self> {
        // Instantiate the circuit.
        let mut circuit = PoSWCircuit::<N>::new(block_template, Uniform::rand(rng))?;

        // Run one iteration of PoSW.
        // Warning: this operation is unchecked.
        let proof = N::posw().prove_once_unchecked(&mut circuit, terminator, rng)?;

        // Construct a block header.
        Ok(Self {
            previous_ledger_root: block_template.previous_ledger_root(),
            transactions_root: block_template.transactions().transactions_root(),
            metadata: BlockHeaderMetadata::new(block_template),
            nonce: circuit.nonce(),
            proof,
        })
    }

    /// Returns `true` if the block header is well-formed.
    pub fn is_valid(&self) -> bool {
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

        // Ensure the nonce is nonzero.
        if self.nonce == Default::default() {
            eprintln!("Invalid nonce in block header");
            return false;
        }

        // Ensure the metadata and proof are valid.
        match self.metadata.height == 0u32 {
            true => self.is_genesis(),
            false => {
                // Ensure the timestamp in the block is greater than 0.
                self.metadata.timestamp > 0i64
                    // Ensure the PoSW proof is valid.
                    && N::posw().verify_from_block_header(self)
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
            // Ensure the cumulative weight in the genesis block is 0u128.
            && self.metadata.cumulative_weight == 0u128
            // Ensure the PoSW proof is valid.
            && N::posw().verify_from_block_header(self)
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

    /// Returns the cumulative weight up to this block (inclusive).
    pub fn cumulative_weight(&self) -> u128 {
        self.metadata.cumulative_weight
    }

    /// Returns the block nonce.
    pub fn nonce(&self) -> N::PoSWNonce {
        self.nonce
    }

    /// Returns the proof, if it is set.
    pub fn proof(&self) -> &PoSWProof<N> {
        &self.proof
    }

    /// Returns the block header size in bytes.
    pub fn size() -> usize {
        N::HEADER_SIZE_IN_BYTES
    }

    /// Returns an instance of the block header tree.
    pub fn to_header_tree(&self) -> Result<MerkleTree<N::BlockHeaderRootParameters>> {
        BlockTemplate::<N>::compute_block_header_tree(self.previous_ledger_root, self.transactions_root, &self.metadata)
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
        let cumulative_weight = <[u8; 16]>::read_le(&mut reader)?;
        let metadata = BlockHeaderMetadata {
            height: u32::from_le_bytes(height),
            timestamp: i64::from_le_bytes(timestamp),
            difficulty_target: u64::from_le_bytes(difficulty_target),
            cumulative_weight: u128::from_le_bytes(cumulative_weight),
        };

        // Read the header nonce.
        let nonce = FromBytes::read_le(&mut reader)?;
        // Read the header proof.
        let proof = FromBytes::read_le(&mut reader)?;

        // Construct the block header.
        Ok(Self::from(previous_ledger_root, transactions_root, metadata, nonce, proof)?)
    }
}

impl<N: Network> ToBytes for BlockHeader<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the header core variables.
        self.previous_ledger_root.write_le(&mut writer)?;
        self.transactions_root.write_le(&mut writer)?;

        // Write the header metadata.
        self.metadata.height.to_le_bytes().write_le(&mut writer)?;
        self.metadata.timestamp.to_le_bytes().write_le(&mut writer)?;
        self.metadata.difficulty_target.to_le_bytes().write_le(&mut writer)?;
        self.metadata.cumulative_weight.to_le_bytes().write_le(&mut writer)?;

        // Write the header nonce.
        self.nonce.write_le(&mut writer)?;
        // Write the header proof.
        self.proof.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for BlockHeader<N> {
    type Err = anyhow::Error;

    fn from_str(header: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(header)?)
    }
}

impl<N: Network> fmt::Display for BlockHeader<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(serde::ser::Error::custom)?)
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
                header.serialize_field("nonce", &self.nonce)?;
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
                Ok(Self::from(
                    serde_json::from_value(header["previous_ledger_root"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["transactions_root"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["metadata"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["nonce"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(header["proof"].clone()).map_err(de::Error::custom)?,
                )
                .map_err(de::Error::custom)?)
            }
            false => FromBytesDeserializer::<Self>::deserialize(deserializer, "block header", N::HEADER_SIZE_IN_BYTES),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet1::Testnet1, testnet2::Testnet2, PoSWScheme};

    use rand::thread_rng;

    /// Returns the expected block header size by summing its expected subcomponents.
    /// Update this method if the contents of a block header have changed.
    fn get_expected_size<N: Network>() -> usize {
        32 // LedgerRoot
            + 32 // TransactionsRoot
            + BlockHeaderMetadata::size()
            + 32 // N::InnerScalarField
            + N::HEADER_PROOF_SIZE_IN_BYTES
    }

    #[test]
    fn test_block_header_size() {
        assert_eq!(get_expected_size::<Testnet1>(), Testnet1::HEADER_SIZE_IN_BYTES);
        assert_eq!(get_expected_size::<Testnet1>(), Testnet1::HEADER_SIZE_IN_BYTES);

        assert_eq!(get_expected_size::<Testnet2>(), Testnet2::HEADER_SIZE_IN_BYTES);
        assert_eq!(get_expected_size::<Testnet2>(), Testnet2::HEADER_SIZE_IN_BYTES);
    }

    #[test]
    fn test_block_header_genesis_size() {
        let block_header = Testnet2::genesis_block().header();
        assert_eq!(block_header.to_bytes_le().unwrap().len(), Testnet2::HEADER_SIZE_IN_BYTES);
        assert_eq!(bincode::serialize(&block_header).unwrap().len(), Testnet2::HEADER_SIZE_IN_BYTES);
    }

    #[test]
    fn test_block_header_serialization() {
        let block_header = Testnet2::genesis_block().header().to_owned();

        // Serialize
        let serialized = block_header.to_bytes_le().unwrap();
        assert_eq!(&serialized[..], &bincode::serialize(&block_header).unwrap()[..]);

        // Deserialize
        let deserialized = BlockHeader::read_le(&serialized[..]).unwrap();
        assert_eq!(deserialized, block_header);
    }

    #[test]
    fn test_block_header_serde_json() {
        let block_header = Testnet2::genesis_block().header().to_owned();

        // Serialize
        let expected_string = block_header.to_string();
        let candidate_string = serde_json::to_string(&block_header).unwrap();
        assert_eq!(1669, candidate_string.len(), "Update me if serialization has changed");
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
        assert_eq!(block_header.metadata.cumulative_weight, 0);

        // Ensure the genesis block does *not* contain the following.
        assert_ne!(block_header.previous_ledger_root, Default::default());
        assert_ne!(block_header.transactions_root, Default::default());
    }

    #[test]
    fn test_block_header_difficulty_target() {
        // Construct the block template.
        let block = Testnet2::genesis_block();
        let block_template = BlockTemplate::new(
            block.previous_block_hash(),
            block.height(),
            block.timestamp(),
            block.difficulty_target(),
            block.cumulative_weight(),
            block.previous_ledger_root(),
            block.transactions().clone(),
            block.to_coinbase_transaction().unwrap().to_records().next().unwrap(),
        );

        // Construct a PoSW proof.
        let mut block_header =
            Testnet2::posw().mine(&block_template, &AtomicBool::new(false), &mut thread_rng()).unwrap();

        // Check that the difficulty target is satisfied.
        assert!(Testnet2::posw().verify_from_block_header(&block_header));

        // Check that the difficulty target is *not* satisfied.
        block_header.metadata.difficulty_target = 0u64;
        assert!(!Testnet2::posw().verify_from_block_header(&block_header));
    }
}
