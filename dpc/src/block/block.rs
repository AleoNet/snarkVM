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

use crate::{Address, AleoAmount, BlockHeader, BlockScheme, Network, Transaction, TransactionScheme, Transactions};
use snarkvm_algorithms::{merkle_tree::MerkleTree, CRH};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::{
    io::{Read, Result as IoResult, Write},
    sync::Arc,
    time::Instant,
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Block<N: Network> {
    /// Hash of the previous block - 32 bytes
    previous_hash: N::BlockHash,
    /// First `HEADER_SIZE` bytes of the block as defined by the encoding used by "block" messages.
    header: BlockHeader<N>,
    /// The block transactions.
    transactions: Transactions<N>,
}

impl<N: Network> BlockScheme for Block<N> {
    type Address = Address<N>;
    type BlockHash = N::BlockHash;
    type Commitment = N::Commitment;
    type CommitmentsRoot = N::CommitmentsRoot;
    type Header = BlockHeader<N>;
    type SerialNumber = N::SerialNumber;
    type SerialNumbersRoot = N::SerialNumbersRoot;
    type Transaction = Transaction<N>;
    type Transactions = Transactions<N>;

    /// Initializes a new block.
    fn new<R: Rng + CryptoRng>(
        previous_block_hash: Self::BlockHash,
        block_height: u32,
        difficulty_target: u64,
        transactions: Self::Transactions,
        serial_numbers_root: Self::SerialNumbersRoot,
        commitments_root: Self::CommitmentsRoot,
        rng: &mut R,
    ) -> Result<Self> {
        assert!(!(*transactions).is_empty(), "Cannot create block with no transactions");

        // Compute the block header.
        let header = BlockHeader::new(
            block_height,
            difficulty_target,
            transactions.to_transactions_root()?,
            serial_numbers_root,
            commitments_root,
            rng,
        )?;

        <Self as BlockScheme>::from(previous_block_hash, header, transactions)
    }

    /// Initializes a new genesis block with one coinbase transaction.
    fn new_genesis<R: Rng + CryptoRng>(recipient: Self::Address, rng: &mut R) -> Result<Self> {
        // Compute the coinbase transaction.
        let start = Instant::now();
        let transactions = Transactions::from(&[Transaction::new_coinbase(recipient, Self::block_reward(0), rng)?])?;
        println!("{} seconds", (Instant::now() - start).as_secs());

        // Compute the transactions root from the transactions.
        let transactions_root = transactions.to_transactions_root()?;

        // Compute the serial numbers root from the transactions.
        let serial_numbers = transactions.to_serial_numbers()?;
        let serial_numbers_tree =
            MerkleTree::new(Arc::new(N::serial_numbers_tree_parameters().clone()), &serial_numbers)?;

        // Compute the commitments root from the transactions.
        let commitments = transactions.to_commitments()?;
        let commitments_tree = MerkleTree::new(Arc::new(N::commitments_tree_parameters().clone()), &commitments)?;

        // Construct the genesis block header metadata.
        let block_height = 0u32;
        let difficulty_target = u64::MAX;

        // Compute the genesis block header.
        let header = BlockHeader::new(
            block_height,
            difficulty_target,
            transactions_root,
            *serial_numbers_tree.root(),
            *commitments_tree.root(),
            rng,
        )?;

        // Construct the genesis block.
        let block = Self {
            previous_hash: Default::default(),
            header,
            transactions,
        };

        // Ensure the genesis block is valid.
        match block.is_genesis() && block.is_valid() {
            true => Ok(block),
            false => Err(anyhow!("Failed to initialize a genesis block")),
        }
    }

    /// Initializes a new block from a given previous hash, header, and transactions list.
    fn from(previous_hash: Self::BlockHash, header: Self::Header, transactions: Self::Transactions) -> Result<Self> {
        // Construct the block.
        let block = Self {
            previous_hash,
            header,
            transactions,
        };

        // Ensure the block is valid.
        match block.is_valid() {
            true => Ok(block),
            false => Err(anyhow!("Failed to initialize a block from given inputs")),
        }
    }

    /// Returns `true` if the block is well-formed.
    fn is_valid(&self) -> bool {
        // Ensure the previous block hash is well-formed.
        if self.height() == 0u32 {
            if self.previous_hash != Default::default() {
                eprintln!("Genesis block must have an empty previous block hash");
                return false;
            }
        } else if self.previous_hash == Default::default() {
            eprintln!("Block must have a non-empty previous block hash");
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
        let coinbase_reward = AleoAmount(0).sub(*coinbase_transaction.value_balance()); // Make it a positive number.
        let block_reward = Self::block_reward(self.height());
        if coinbase_reward < block_reward {
            eprintln!("Coinbase reward must be >= {}, found {}", block_reward, coinbase_reward);
            return false;
        }

        // Ensure the coinbase reward less transaction fees is less than or equal to the block reward.
        match self.transactions.to_net_value_balance() {
            Ok(net_value_balance) => {
                let candidate_block_reward = AleoAmount(0).sub(net_value_balance); // Make it a positive number.
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

        // Ensure the header and transactions are valid.
        self.header.is_valid() && self.transactions.is_valid()
    }

    /// Returns `true` if the block is a genesis block.
    fn is_genesis(&self) -> bool {
        // Ensure the header is a genesis block header.
        self.header.is_genesis()
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
        preimage.extend_from_slice(&self.header.to_header_root()?.to_bytes_le()?);

        Ok(N::block_hash_crh().hash(&preimage)?)
    }

    /// Returns the serial numbers in the block, by constructing a flattened list of serial numbers from all transactions.
    fn to_serial_numbers(&self) -> Result<Vec<Self::SerialNumber>> {
        self.transactions.to_serial_numbers()
    }

    /// Returns the commitments in the block, by constructing a flattened list of commitments from all transactions.
    fn to_commitments(&self) -> Result<Vec<Self::Commitment>> {
        self.transactions.to_commitments()
    }

    /// Returns the coinbase transaction for the block.
    fn to_coinbase_transaction(&self) -> Result<Self::Transaction> {
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
}

impl<N: Network> Block<N> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet2::Testnet2, Account, AccountScheme};

    use rand::{thread_rng, Rng};

    const ITERATIONS: usize = 1000;

    #[test]
    fn test_block_genesis() {
        let rng = &mut thread_rng();

        let account = Account::<Testnet2>::new(rng).unwrap();
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
}
