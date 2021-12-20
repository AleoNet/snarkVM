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
    Address,
    AleoAmount,
    BlockError,
    BlockHeader,
    BlockTemplate,
    LedgerProof,
    LedgerTree,
    LedgerTreeScheme,
    Network,
    Transaction,
    Transactions,
};
use snarkvm_algorithms::CRH;
use snarkvm_utilities::{to_bytes_le, FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use serde::{de, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
    sync::atomic::AtomicBool,
    time::Instant,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block<N: Network> {
    /// Hash of this block.
    block_hash: N::BlockHash,
    /// Hash of the previous block.
    previous_block_hash: N::BlockHash,
    /// The block header containing the state of the ledger at this block.
    header: BlockHeader<N>,
    /// The block transactions.
    transactions: Transactions<N>,
}

impl<N: Network> Block<N> {
    /// Initializes a new block.
    pub fn new(template: &BlockTemplate<N>, header: BlockHeader<N>) -> Result<Self> {
        assert!(
            !(*template.transactions()).is_empty(),
            "Cannot create block with no transactions"
        );

        // Prepare the variables.
        let previous_block_hash = template.previous_block_hash();
        let transactions = template.transactions().clone();

        Ok(Self::from(previous_block_hash, header, transactions)?)
    }

    /// Initializes a new block.
    pub fn mine<R: Rng + CryptoRng>(template: BlockTemplate<N>, terminator: &AtomicBool, rng: &mut R) -> Result<Self> {
        assert!(
            !(*template.transactions()).is_empty(),
            "Cannot create block with no transactions"
        );

        // Compute the block header.
        let header = BlockHeader::mine(&template, terminator, rng)?;

        Ok(Self::new(&template, header)?)
    }

    /// Initializes a new genesis block with one coinbase transaction.
    pub fn new_genesis<R: Rng + CryptoRng>(recipient: Address<N>, rng: &mut R) -> Result<Self> {
        // Compute the coinbase transaction.
        let start = Instant::now();
        let (transaction, _) = Transaction::new_coinbase(recipient, Self::block_reward(0), true, rng)?;
        let transactions = Transactions::from(&[transaction])?;
        println!("{} seconds", (Instant::now() - start).as_secs());

        // Construct the genesis block header metadata.
        let block_height = 0u32;
        let block_timestamp = 0i64;
        let difficulty_target = u64::MAX;
        let cumulative_weight = 0u128;

        // Construct the block template.
        let template = BlockTemplate::new(
            LedgerProof::<N>::default().block_hash(),
            block_height,
            block_timestamp,
            difficulty_target,
            cumulative_weight,
            LedgerTree::<N>::new()?.root(),
            transactions,
        );

        // Construct the genesis block.
        let block = Self::mine(template, &AtomicBool::new(false), rng)?;

        // Ensure the block is valid genesis block.
        match block.is_genesis() {
            true => Ok(block),
            false => Err(anyhow!("Failed to initialize a genesis block")),
        }
    }

    /// Initializes a new block from a given previous hash, header, and transactions list.
    pub fn from(
        previous_block_hash: N::BlockHash,
        header: BlockHeader<N>,
        transactions: Transactions<N>,
    ) -> Result<Self, BlockError> {
        // Compute the block hash.
        let block_hash = N::block_hash_crh()
            .hash(&to_bytes_le![previous_block_hash, header.to_header_root()?]?)?
            .into();

        // Construct the block.
        let block = Self {
            block_hash,
            previous_block_hash,
            header,
            transactions,
        };

        // Ensure the block is valid.
        match block.is_valid() {
            true => Ok(block),
            false => Err(anyhow!("Failed to initialize a block from given inputs").into()),
        }
    }

    /// Returns `true` if the block is well-formed.
    pub fn is_valid(&self) -> bool {
        // Ensure the previous block hash is well-formed.
        let genesis_previous_block_hash = LedgerProof::<N>::default().block_hash();
        if self.height() == 0u32 {
            if self.previous_block_hash != genesis_previous_block_hash {
                eprintln!("Genesis block must have the default ledger proof block hash");
                return false;
            }
        } else if self.previous_block_hash == genesis_previous_block_hash {
            eprintln!("Block cannot have genesis previous block hash");
            return false;
        } else if self.previous_block_hash == Default::default() {
            eprintln!("Block must have a non-empty previous block hash");
            return false;
        }

        // Ensure the header are valid.
        if !self.header.is_valid() {
            eprintln!("Invalid block header");
            return false;
        }

        // Ensure the transactions are valid.
        if !self.transactions.is_valid() {
            eprintln!("Invalid block transactions");
            return false;
        }

        // Ensure the transactions root matches the computed root from the transactions list.
        if self.header.transactions_root() != self.transactions.transactions_root() {
            eprintln!("Invalid block transactions does not match transactions root in header");
            return false;
        }

        // Retrieve the coinbase transaction.
        let coinbase_transaction = match self.to_coinbase_transaction() {
            Ok(coinbase_transaction) => coinbase_transaction,
            Err(error) => {
                eprintln!("{}", error);
                return false;
            }
        };

        // Ensure the coinbase reward is equal to or greater than the expected block reward.
        let coinbase_reward = AleoAmount::ZERO.sub(coinbase_transaction.value_balance()); // Make it a positive number.
        let block_reward = Self::block_reward(self.height());
        if coinbase_reward < block_reward {
            eprintln!("Coinbase reward must be >= {}, found {}", block_reward, coinbase_reward);
            return false;
        }

        // Ensure the coinbase reward less transaction fees is less than or equal to the block reward.
        let candidate_block_reward = AleoAmount::ZERO.sub(self.transactions.net_value_balance()); // Make it a positive number.
        if candidate_block_reward > block_reward {
            eprintln!("Block reward must be <= {}", block_reward);
            return false;
        }

        true
    }

    /// Returns `true` if the block is a genesis block.
    pub fn is_genesis(&self) -> bool {
        // Ensure the header is a genesis block header.
        self.header.is_genesis()
    }

    /// Returns the hash of this block.
    pub fn hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the previous block hash.
    pub fn previous_block_hash(&self) -> N::BlockHash {
        self.previous_block_hash
    }

    /// Returns the header.
    pub fn header(&self) -> &BlockHeader<N> {
        &self.header
    }

    /// Returns the transactions.
    pub fn transactions(&self) -> &Transactions<N> {
        &self.transactions
    }

    /// Returns the previous ledger root from the block header.
    pub fn previous_ledger_root(&self) -> N::LedgerRoot {
        self.header.previous_ledger_root()
    }

    /// Returns the transactions root in the block header.
    pub fn transactions_root(&self) -> N::TransactionsRoot {
        self.header.transactions_root()
    }

    /// Returns the block height.
    pub fn height(&self) -> u32 {
        self.header.height()
    }

    /// Returns the block timestamp.
    pub fn timestamp(&self) -> i64 {
        self.header.timestamp()
    }

    /// Returns the block difficulty target.
    pub fn difficulty_target(&self) -> u64 {
        self.header.difficulty_target()
    }

    /// Returns the cumulative weight up to this block (inclusive).
    pub fn cumulative_weight(&self) -> u128 {
        self.header.cumulative_weight()
    }

    /// Returns the block nonce.
    pub fn nonce(&self) -> N::PoSWNonce {
        self.header.nonce()
    }

    /// Returns the serial numbers in the block, by constructing a flattened list of serial numbers from all transactions.
    pub fn serial_numbers(&self) -> impl Iterator<Item = &N::SerialNumber> + '_ {
        self.transactions.serial_numbers()
    }

    /// Returns the commitments in the block, by constructing a flattened list of commitments from all transactions.
    pub fn commitments(&self) -> impl Iterator<Item = &N::Commitment> + '_ {
        self.transactions.commitments()
    }

    /// Returns the coinbase transaction for the block.
    pub fn to_coinbase_transaction(&self) -> Result<Transaction<N>> {
        // Filter out all transactions with a positive value balance.
        let coinbase_transaction: Vec<_> = self
            .transactions
            .iter()
            .filter(|t| t.value_balance().is_negative())
            .collect();

        // Ensure there is exactly 1 coinbase transaction.
        let num_coinbase = coinbase_transaction.len();
        match num_coinbase == 1 {
            true => Ok(coinbase_transaction[0].clone()),
            false => Err(anyhow!(
                "Block must have 1 coinbase transaction, found {}",
                num_coinbase
            )),
        }
    }

    ///
    /// Returns the block reward for the given block height.
    ///
    pub fn block_reward(height: u32) -> AleoAmount {
        match height == 0 {
            true => {
                // Output the starting supply as the genesis block reward.
                AleoAmount::from_i64(N::ALEO_STARTING_SUPPLY_IN_CREDITS * AleoAmount::ONE_CREDIT.0)
            }
            false => {
                // The initial blocks that aren't taken into account with the halving calculation.
                // The time it takes before the halving - 4,730,400 blocks (approximately 3 years).
                let expected_blocks_per_hour: u32 = 3600 / (N::ALEO_BLOCK_TIME_IN_SECS as u32);
                let num_years = 3;
                let block_segments = num_years * 365 * 24 * expected_blocks_per_hour;

                // The block reward halves at most 2 times - minimum is 25 ALEO.
                // The reward will halve at blocks `4,730,400` and `9,460,800`.
                // Blocks 1 to 4,730,400         - 100 CREDITS
                // Blocks 4,730,401 to 9,460,800 - 50 CREDITS
                // Blocks 9,460,801+             - 25 CREDITS
                let initial_reward = 100i64 * AleoAmount::ONE_CREDIT.0;
                let num_halves = u32::min(height.saturating_sub(1) / block_segments, 2);
                let reward = initial_reward / (2_u64.pow(num_halves)) as i64;

                AleoAmount::from_i64(reward)
            }
        }
    }
}

impl<N: Network> FromBytes for Block<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let block_hash: N::BlockHash = FromBytes::read_le(&mut reader)?;
        let previous_block_hash = FromBytes::read_le(&mut reader)?;
        let header = FromBytes::read_le(&mut reader)?;
        let transactions = FromBytes::read_le(&mut reader)?;
        let block = Self::from(previous_block_hash, header, transactions)?;

        match block_hash == block.hash() {
            true => Ok(block),
            false => Err(BlockError::Message("Mismatching block hash, possible data corruption".to_string()).into()),
        }
    }
}

impl<N: Network> ToBytes for Block<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.block_hash.write_le(&mut writer)?;
        self.previous_block_hash.write_le(&mut writer)?;
        self.header.write_le(&mut writer)?;
        self.transactions.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for Block<N> {
    type Err = anyhow::Error;

    fn from_str(block: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(&block)?)
    }
}

impl<N: Network> fmt::Display for Block<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            serde_json::to_string(self).map_err::<fmt::Error, _>(serde::ser::Error::custom)?
        )
    }
}

impl<N: Network> Serialize for Block<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut block = serializer.serialize_struct("Block", 4)?;
                block.serialize_field("block_hash", &self.block_hash)?;
                block.serialize_field("previous_block_hash", &self.previous_block_hash)?;
                block.serialize_field("header", &self.header)?;
                block.serialize_field("transactions", &self.transactions)?;
                block.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Block<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let block = serde_json::Value::deserialize(deserializer)?;
                let block_hash: N::BlockHash =
                    serde_json::from_value(block["block_hash"].clone()).map_err(de::Error::custom)?;

                // Recover the block.
                let block = Self::from(
                    serde_json::from_value(block["previous_block_hash"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(block["header"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(block["transactions"].clone()).map_err(de::Error::custom)?,
                )
                .map_err(de::Error::custom)?;

                // Ensure the block hash matches.
                match block_hash == block.hash() {
                    true => Ok(block),
                    false => {
                        Err(anyhow!("Mismatching block hash, possible data corruption")).map_err(de::Error::custom)
                    }
                }
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "block"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet2::Testnet2, Account, AccountScheme};
    use snarkvm_utilities::UniformRand;

    use rand::{thread_rng, Rng};
    use rayon::iter::{IntoParallelIterator, ParallelIterator};
    use std::str::FromStr;

    const ITERATIONS: usize = 1000;

    #[test]
    fn test_block_genesis() {
        let rng = &mut thread_rng();

        let account = Account::<Testnet2>::new(rng);
        let genesis_block = Block::<Testnet2>::new_genesis(account.address(), rng).unwrap();
        println!("{:?}", genesis_block);
    }

    #[test]
    fn test_block_rewards() {
        let rng = &mut thread_rng();

        let first_halving: u32 = 3 * 365 * 24 * 180; // 4,730,400
        let second_halving: u32 = first_halving * 2; // 9,460,800

        // Genesis

        assert_eq!(
            Block::<Testnet2>::block_reward(0).0,
            Testnet2::ALEO_STARTING_SUPPLY_IN_CREDITS * 1_000_000
        );

        // Before block halving

        let mut block_reward: i64 = 100 * 1_000_000;

        for _ in 0..ITERATIONS {
            let block_height: u32 = rng.gen_range(1..first_halving);
            assert_eq!(Block::<Testnet2>::block_reward(block_height).0, block_reward);
        }
        assert_eq!(Block::<Testnet2>::block_reward(first_halving).0, block_reward);

        // First block halving

        block_reward /= 2;

        assert_eq!(Block::<Testnet2>::block_reward(first_halving + 1).0, block_reward);
        for _ in 0..ITERATIONS {
            let block_num: u32 = rng.gen_range((first_halving + 1)..second_halving);
            assert_eq!(Block::<Testnet2>::block_reward(block_num).0, block_reward);
        }
        assert_eq!(Block::<Testnet2>::block_reward(second_halving).0, block_reward);

        // Second and final block halving

        block_reward /= 2;

        assert_eq!(Block::<Testnet2>::block_reward(second_halving + 1).0, block_reward);
        for _ in 0..ITERATIONS {
            let block_num: u32 = rng.gen_range(second_halving..u32::MAX);
            assert_eq!(Block::<Testnet2>::block_reward(block_num).0, block_reward);
        }
        assert_eq!(Block::<Testnet2>::block_reward(u32::MAX).0, block_reward);
    }

    #[test]
    fn test_token_supply() {
        let first_halving: u32 = 3 * 365 * 24 * 180; // 4,730,400
        let supply_at_first_halving = 1_473_040_000;

        let second_halving: u32 = first_halving * 2; // 9,460,800
        let supply_at_second_halving = 1_709_560_000;

        assert_eq!(
            Block::<Testnet2>::block_reward(0),
            AleoAmount::from_i64(Testnet2::ALEO_STARTING_SUPPLY_IN_CREDITS * AleoAmount::ONE_CREDIT.0)
        );

        let mut supply = AleoAmount::ZERO;

        // Phase 1 - 100 credits per block.
        let phase_1_sum = AleoAmount::from_i64(
            (0..=first_halving)
                .into_par_iter()
                .map(|i| Block::<Testnet2>::block_reward(i).0)
                .sum::<i64>(),
        );

        supply = supply.add(phase_1_sum);

        assert_eq!(
            supply,
            AleoAmount::from_i64(supply_at_first_halving * AleoAmount::ONE_CREDIT.0)
        );

        // Phase 2 - 50 credits per block.
        let phase_2_sum = AleoAmount::from_i64(
            ((first_halving + 1)..=second_halving)
                .into_par_iter()
                .map(|i| Block::<Testnet2>::block_reward(i).0)
                .sum::<i64>(),
        );

        supply = supply.add(phase_2_sum);

        assert_eq!(
            supply,
            AleoAmount::from_i64(supply_at_second_halving * AleoAmount::ONE_CREDIT.0)
        );
    }

    #[test]
    fn test_block_serde_json() {
        let rng = &mut thread_rng();
        let account = Account::<Testnet2>::new(rng);
        let expected_block = Block::<Testnet2>::new_genesis(account.address(), rng).unwrap();

        // Serialize
        let expected_string = expected_block.to_string();
        let candidate_string = serde_json::to_string(&expected_block).unwrap();
        assert_eq!(4169, candidate_string.len(), "Update me if serialization has changed");
        assert_eq!(expected_string, candidate_string);

        // Deserialize
        assert_eq!(expected_block, Block::<Testnet2>::from_str(&candidate_string).unwrap());
        assert_eq!(expected_block, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_block_bincode() {
        let rng = &mut thread_rng();
        let account = Account::<Testnet2>::new(rng);
        let expected_block = Block::<Testnet2>::new_genesis(account.address(), rng).unwrap();

        // Serialize
        let expected_bytes = expected_block.to_bytes_le().unwrap();
        let candidate_bytes = bincode::serialize(&expected_block).unwrap();
        assert_eq!(2090, expected_bytes.len(), "Update me if serialization has changed");
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

        // Deserialize
        assert_eq!(expected_block, Block::<Testnet2>::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_block, bincode::deserialize(&candidate_bytes[..]).unwrap());
    }

    /// A bech32-encoded representation of the block hash.
    #[test]
    fn test_block_hash_serde_json() {
        let rng = &mut thread_rng();
        let expected_block_hash: <Testnet2 as Network>::BlockHash = UniformRand::rand(rng);

        // Serialize
        let expected_string = &expected_block_hash.to_string();
        let candidate_string = serde_json::to_string(&expected_block_hash).unwrap();
        let sanitized_candidate_string = serde_json::Value::from_str(&candidate_string).unwrap();
        let sanitized_candidate_string = sanitized_candidate_string.as_str().unwrap();
        println!("{} == {}", expected_string, sanitized_candidate_string);
        assert_eq!(
            61,
            sanitized_candidate_string.len(),
            "Update me if serialization has changed"
        );
        assert_eq!(expected_string, sanitized_candidate_string);

        // Deserialize
        assert_eq!(
            expected_block_hash,
            <Testnet2 as Network>::BlockHash::from_str(&expected_string).unwrap()
        );
        assert_eq!(expected_block_hash, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_block_hash_bincode() {
        let rng = &mut thread_rng();
        let expected_block_hash: <Testnet2 as Network>::BlockHash = UniformRand::rand(rng);

        // Serialize
        let expected_bytes = expected_block_hash.to_bytes_le().unwrap();
        assert_eq!(32, expected_bytes.len(), "Update me if serialization has changed");
        assert_eq!(
            &expected_bytes[..],
            &bincode::serialize(&expected_block_hash).unwrap()[..]
        );

        // Deserialize
        assert_eq!(
            expected_block_hash,
            <Testnet2 as Network>::BlockHash::read_le(&expected_bytes[..]).unwrap()
        );
        assert_eq!(expected_block_hash, bincode::deserialize(&expected_bytes[..]).unwrap());
    }
}
