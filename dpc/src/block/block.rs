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
    LedgerProof,
    LedgerTree,
    LedgerTreeScheme,
    Network,
    Transaction,
    Transactions,
};
use snarkvm_algorithms::CRH;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};
use std::{
    io::{Read, Result as IoResult, Write},
    sync::atomic::AtomicBool,
    time::Instant,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
    pub fn mine<R: Rng + CryptoRng>(
        previous_block_hash: N::BlockHash,
        block_height: u32,
        block_timestamp: i64,
        difficulty_target: u64,
        previous_ledger_root: N::LedgerRoot,
        transactions: Transactions<N>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<Self> {
        assert!(!(*transactions).is_empty(), "Cannot create block with no transactions");

        // Compute the block header.
        let header = BlockHeader::mine(
            block_height,
            block_timestamp,
            difficulty_target,
            previous_ledger_root,
            transactions.to_transactions_root()?,
            terminator,
            rng,
        )?;

        Ok(Self::from(previous_block_hash, header, transactions)?)
    }

    /// Initializes a new genesis block with one coinbase transaction.
    pub fn new_genesis<R: Rng + CryptoRng>(recipient: Address<N>, rng: &mut R) -> Result<Self> {
        // Compute the coinbase transaction.
        let start = Instant::now();
        let transactions = Transactions::from(&[Transaction::new_coinbase(recipient, Self::block_reward(0), rng)?])?;
        println!("{} seconds", (Instant::now() - start).as_secs());

        // Compute the transactions root from the transactions.
        let transactions_root = transactions.to_transactions_root()?;

        // Construct the genesis block header metadata.
        let block_height = 0u32;
        let block_timestamp = 0i64;
        let difficulty_target = u64::MAX;

        // Compute the genesis block header.
        let header = BlockHeader::mine(
            block_height,
            block_timestamp,
            difficulty_target,
            LedgerTree::<N>::new()?.root(),
            transactions_root,
            &AtomicBool::new(false),
            rng,
        )?;

        // Construct the previous block hash.
        let previous_block_hash = LedgerProof::<N>::default().block_hash();

        // Construct the genesis block.
        let block = Self::from(previous_block_hash, header, transactions)?;

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

        // Fetch the transactions root.
        let transactions_root = match self.transactions.to_transactions_root() {
            Ok(transactions_root) => transactions_root,
            Err(error) => {
                eprintln!("{}", error);
                return false;
            }
        };

        // Ensure the transactions root matches the computed root from the transactions list.
        if self.header.transactions_root() != transactions_root {
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
        match self.transactions.to_net_value_balance() {
            Ok(net_value_balance) => {
                let candidate_block_reward = AleoAmount::ZERO.sub(net_value_balance); // Make it a positive number.
                if candidate_block_reward > block_reward {
                    eprintln!("Block reward must be <= {}", block_reward);
                    return false;
                }
            }
            Err(error) => {
                eprintln!("{}", error);
                return false;
            }
        };

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

    /// Returns the block nonce.
    pub fn nonce(&self) -> N::InnerScalarField {
        self.header.nonce()
    }

    /// Returns the serial numbers in the block, by constructing a flattened list of serial numbers from all transactions.
    pub fn serial_numbers(&self) -> Vec<N::SerialNumber> {
        self.transactions.serial_numbers().collect()
    }

    /// Returns the commitments in the block, by constructing a flattened list of commitments from all transactions.
    pub fn commitments(&self) -> Vec<N::Commitment> {
        self.transactions.commitments().collect()
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
    /// TODO (howardwu): CRITICAL - Update this with the correct emission schedule.
    ///
    pub fn block_reward(height: u32) -> AleoAmount {
        match height == 0 {
            true => {
                // Output the starting supply as the genesis block reward.
                AleoAmount::from_bytes(N::ALEO_STARTING_SUPPLY_IN_CREDITS * AleoAmount::ONE_CREDIT.0)
            }
            false => {
                let expected_blocks_per_hour: u32 = 180;
                let num_years = 3;
                let block_segments = num_years * 365 * 24 * expected_blocks_per_hour;

                // The block reward halves at most 2 times - minimum is 37.5 ALEO after 8 years.
                let initial_reward = 150i64 * AleoAmount::ONE_CREDIT.0;
                let num_halves = u32::min(height / block_segments, 2);
                let reward = initial_reward / (2_u64.pow(num_halves)) as i64;

                AleoAmount::from_bytes(reward)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet2::Testnet2, Account, AccountScheme};
    use snarkvm_utilities::UniformRand;

    use rand::{thread_rng, Rng};
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

        let first_halving: u32 = 3 * 365 * 24 * 180;
        let second_halving: u32 = first_halving * 2;

        // Genesis

        assert_eq!(
            Block::<Testnet2>::block_reward(0).0,
            Testnet2::ALEO_STARTING_SUPPLY_IN_CREDITS * 1_000_000
        );

        // Before block halving

        let mut block_reward: i64 = 150 * 1_000_000;

        for _ in 0..ITERATIONS {
            let block_height: u32 = rng.gen_range(0..first_halving);
            assert_eq!(Block::<Testnet2>::block_reward(block_height).0, block_reward);
        }

        // First block halving

        block_reward /= 2;

        assert_eq!(Block::<Testnet2>::block_reward(first_halving).0, block_reward);

        for _ in 0..ITERATIONS {
            let block_num: u32 = rng.gen_range((first_halving + 1)..second_halving);
            assert_eq!(Block::<Testnet2>::block_reward(block_num).0, block_reward);
        }

        // Second and final block halving

        block_reward /= 2;

        assert_eq!(Block::<Testnet2>::block_reward(second_halving).0, block_reward);
        assert_eq!(Block::<Testnet2>::block_reward(u32::MAX).0, block_reward);

        for _ in 0..ITERATIONS {
            let block_num: u32 = rng.gen_range(second_halving..u32::MAX);
            assert_eq!(Block::<Testnet2>::block_reward(block_num).0, block_reward);
        }
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
