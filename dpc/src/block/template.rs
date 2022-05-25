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

use crate::{BlockHeaderMetadata, Network, Record, Transactions};
use snarkvm_algorithms::merkle_tree::MerkleTree;
use snarkvm_utilities::{FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::Result;
use serde::{de, ser, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
    sync::Arc,
};

///
/// The block template used by miners to mine the next block.
///
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockTemplate<N: Network> {
    previous_block_hash: N::BlockHash,
    block_height: u32,
    block_timestamp: i64,
    difficulty_target: u64,
    cumulative_weight: u128,
    previous_ledger_root: N::LedgerRoot,
    transactions: Transactions<N>,
    coinbase_record: Record<N>,
}

impl<N: Network> BlockTemplate<N> {
    /// Initializes a new block template.
    pub fn new(
        previous_block_hash: N::BlockHash,
        block_height: u32,
        block_timestamp: i64,
        difficulty_target: u64,
        cumulative_weight: u128,
        previous_ledger_root: N::LedgerRoot,
        transactions: Transactions<N>,
        coinbase_record: Record<N>,
    ) -> Self {
        assert!(!(*transactions).is_empty(), "Cannot create a block with no transactions");

        Self {
            previous_block_hash,
            block_height,
            block_timestamp,
            difficulty_target,
            cumulative_weight,
            previous_ledger_root,
            transactions,
            coinbase_record,
        }
    }

    /// Returns the previous block hash.
    pub fn previous_block_hash(&self) -> N::BlockHash {
        self.previous_block_hash
    }

    /// Returns the block height.
    pub fn block_height(&self) -> u32 {
        self.block_height
    }

    /// Returns the block timestamp.
    pub fn block_timestamp(&self) -> i64 {
        self.block_timestamp
    }

    /// Returns the difficulty target.
    pub fn difficulty_target(&self) -> u64 {
        self.difficulty_target
    }

    /// Returns the cumulative weight.
    pub fn cumulative_weight(&self) -> u128 {
        self.cumulative_weight
    }

    /// Returns the previous ledger root.
    pub fn previous_ledger_root(&self) -> N::LedgerRoot {
        self.previous_ledger_root
    }

    /// Returns a reference to the block transactions.
    pub fn transactions(&self) -> &Transactions<N> {
        &self.transactions
    }

    /// Returns the coinbase record in the block transactions.
    pub fn coinbase_record(&self) -> &Record<N> {
        &self.coinbase_record
    }

    /// Returns an instance of the block header tree.
    pub fn to_header_tree(&self) -> Result<MerkleTree<N::BlockHeaderRootParameters>> {
        Self::compute_block_header_tree(
            self.previous_ledger_root,
            self.transactions.transactions_root(),
            &BlockHeaderMetadata::new(self),
        )
    }

    /// Returns the block header root.
    pub fn to_header_root(&self) -> Result<N::BlockHeaderRoot> {
        Ok((*self.to_header_tree()?.root()).into())
    }

    /// Returns an instance of the block header tree.
    pub fn compute_block_header_tree(
        previous_ledger_root: N::LedgerRoot,
        transactions_root: N::TransactionsRoot,
        metadata: &BlockHeaderMetadata,
    ) -> Result<MerkleTree<N::BlockHeaderRootParameters>> {
        let previous_ledger_root = previous_ledger_root.to_bytes_le()?;
        assert_eq!(previous_ledger_root.len(), 32);

        let transactions_root = transactions_root.to_bytes_le()?;
        assert_eq!(transactions_root.len(), 32);

        let metadata = metadata.to_bytes_le()?;
        assert_eq!(metadata.len(), 36);

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
}

impl<N: Network> FromBytes for BlockTemplate<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let previous_block_hash: N::BlockHash = FromBytes::read_le(&mut reader)?;
        let block_height: u32 = FromBytes::read_le(&mut reader)?;
        let block_timestamp: i64 = FromBytes::read_le(&mut reader)?;
        let difficulty_target: u64 = FromBytes::read_le(&mut reader)?;
        let cumulative_weight: u128 = FromBytes::read_le(&mut reader)?;
        let previous_ledger_root: N::LedgerRoot = FromBytes::read_le(&mut reader)?;
        let transactions: Transactions<N> = FromBytes::read_le(&mut reader)?;
        let coinbase_record: Record<N> = FromBytes::read_le(&mut reader)?;

        Ok(Self::new(
            previous_block_hash,
            block_height,
            block_timestamp,
            difficulty_target,
            cumulative_weight,
            previous_ledger_root,
            transactions,
            coinbase_record,
        ))
    }
}

impl<N: Network> ToBytes for BlockTemplate<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.previous_block_hash.write_le(&mut writer)?;
        self.block_height.write_le(&mut writer)?;
        self.block_timestamp.write_le(&mut writer)?;
        self.difficulty_target.write_le(&mut writer)?;
        self.cumulative_weight.write_le(&mut writer)?;
        self.previous_ledger_root.write_le(&mut writer)?;
        self.transactions.write_le(&mut writer)?;
        self.coinbase_record.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for BlockTemplate<N> {
    type Err = anyhow::Error;

    fn from_str(transactions: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(transactions)?)
    }
}

impl<N: Network> fmt::Display for BlockTemplate<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(ser::Error::custom)?)
    }
}

impl<N: Network> Serialize for BlockTemplate<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut block_template = serializer.serialize_struct("BlockTemplate", 7)?;
                block_template.serialize_field("previous_block_hash", &self.previous_block_hash)?;
                block_template.serialize_field("block_height", &self.block_height)?;
                block_template.serialize_field("block_timestamp", &self.block_timestamp)?;
                block_template.serialize_field("difficulty_target", &self.difficulty_target)?;
                block_template.serialize_field("cumulative_weight", &self.cumulative_weight)?;
                block_template.serialize_field("previous_ledger_root", &self.previous_ledger_root)?;
                block_template.serialize_field("transactions", &self.transactions)?;
                block_template.serialize_field("coinbase_record", &self.coinbase_record)?;
                block_template.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for BlockTemplate<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let block_template = serde_json::Value::deserialize(deserializer)?;
                let previous_block_hash: N::BlockHash =
                    serde_json::from_value(block_template["previous_block_hash"].clone()).map_err(de::Error::custom)?;
                let block_height: u32 =
                    serde_json::from_value(block_template["block_height"].clone()).map_err(de::Error::custom)?;
                let block_timestamp: i64 =
                    serde_json::from_value(block_template["block_timestamp"].clone()).map_err(de::Error::custom)?;
                let difficulty_target: u64 =
                    serde_json::from_value(block_template["difficulty_target"].clone()).map_err(de::Error::custom)?;
                let cumulative_weight: u128 =
                    serde_json::from_value(block_template["cumulative_weight"].clone()).map_err(de::Error::custom)?;
                let previous_ledger_root: N::LedgerRoot =
                    serde_json::from_value(block_template["previous_ledger_root"].clone())
                        .map_err(de::Error::custom)?;
                let transactions: Transactions<N> =
                    serde_json::from_value(block_template["transactions"].clone()).map_err(de::Error::custom)?;
                let coinbase_record: Record<N> =
                    serde_json::from_value(block_template["coinbase_record"].clone()).map_err(de::Error::custom)?;
                Ok(Self::new(
                    previous_block_hash,
                    block_height,
                    block_timestamp,
                    difficulty_target,
                    cumulative_weight,
                    previous_ledger_root,
                    transactions,
                    coinbase_record,
                ))
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "block template"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;

    #[test]
    fn test_template_serde_json() {
        // Construct the block template.
        let block = Testnet2::genesis_block();
        let expected_template = BlockTemplate::new(
            block.previous_block_hash(),
            block.height(),
            block.timestamp(),
            block.difficulty_target(),
            block.cumulative_weight(),
            block.previous_ledger_root(),
            block.transactions().clone(),
            block.to_coinbase_transaction().unwrap().to_records().next().unwrap(),
        );

        // Serialize
        let expected_string = expected_template.to_string();
        let candidate_string = serde_json::to_string(&expected_template).unwrap();
        assert_eq!(4012, candidate_string.len(), "Update me if serialization has changed");
        assert_eq!(expected_string, candidate_string);

        // Deserialize
        assert_eq!(expected_template, BlockTemplate::<Testnet2>::from_str(&candidate_string).unwrap());
        assert_eq!(expected_template, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_template_bincode() {
        // Construct the block template.
        let block = Testnet2::genesis_block();
        let expected_template = BlockTemplate::new(
            block.previous_block_hash(),
            block.height(),
            block.timestamp(),
            block.difficulty_target(),
            block.cumulative_weight(),
            block.previous_ledger_root(),
            block.transactions().clone(),
            block.to_coinbase_transaction().unwrap().to_records().next().unwrap(),
        );

        // Serialize
        let expected_bytes = expected_template.to_bytes_le().unwrap();
        let candidate_bytes = bincode::serialize(&expected_template).unwrap();
        assert_eq!(1853, expected_bytes.len(), "Update me if serialization has changed");
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

        // Deserialize
        assert_eq!(expected_template, BlockTemplate::<Testnet2>::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_template, bincode::deserialize(&candidate_bytes[..]).unwrap());
    }
}
