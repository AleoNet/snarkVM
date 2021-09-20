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
    BlockHeader,
    BlockScheme,
    BlockTransactions,
    DPCScheme,
    LedgerProof,
    Network,
    StateTransition,
    TransactionScheme,
    DPC,
};
use snarkvm_algorithms::CRH;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::io::{Read, Result as IoResult, Write};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Block<N: Network> {
    /// Hash of the previous block - 32 bytes
    pub previous_hash: N::BlockHash,
    /// First `HEADER_SIZE` bytes of the block as defined by the encoding used by "block" messages.
    pub header: BlockHeader<N>,
    /// The block transactions.
    pub transactions: BlockTransactions<N>,
}

impl<N: Network> BlockScheme for Block<N> {
    type Address = Address<N>;
    type BlockHash = N::BlockHash;
    type Commitment = N::Commitment;
    type Header = BlockHeader<N>;
    type SerialNumber = N::SerialNumber;
    type Transactions = BlockTransactions<N>;

    fn new_genesis<R: Rng + CryptoRng>(recipient: Self::Address, rng: &mut R) -> Result<Self> {
        // Compute the coinbase transaction.
        let transaction = {
            let amount = Self::block_reward(0);
            let state = StateTransition::new_coinbase(recipient, amount, rng)?;
            let authorization = DPC::<N>::authorize(&vec![], &state, rng)?;
            DPC::<N>::execute(authorization, state.executables(), &LedgerProof::default(), rng)?
        };

        // Compute the genesis block.
        let transactions = BlockTransactions::from(&[transaction]);
        let header = BlockHeader::new_genesis(&transactions, rng)?;
        let block = Self {
            previous_hash: Default::default(),
            header,
            transactions,
        };

        // Ensure the genesis block is valid.
        match block.is_valid() {
            true => Ok(block),
            false => Err(anyhow!("Failed to initialize a genesis block")),
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
        } else {
            if self.previous_hash == Default::default() {
                eprintln!("Block must have a non-empty previous block hash");
                return false;
            }
        }

        // Retrieve the coinbase transaction.
        let coinbase_transaction = {
            // Filter out all transactions with a positive value balance.
            let coinbase_transaction: Vec<_> = self
                .transactions
                .iter()
                .filter(|t| t.value_balance().is_negative())
                .collect();

            // Ensure there is exactly one coinbase transaction.
            let num_coinbase = coinbase_transaction.len();
            match num_coinbase == 1 {
                true => coinbase_transaction[0],
                false => {
                    eprintln!("Block must have one coinbase transaction, found {}", num_coinbase);
                    return false;
                }
            }
        };

        // Ensure the coinbase transaction contains a coinbase reward
        // that is equal to or greater than the expected block reward.
        let coinbase_reward = AleoAmount(0).sub(*coinbase_transaction.value_balance()); // Make it a positive number.
        let block_reward = Self::block_reward(self.height());
        if coinbase_reward < block_reward {
            eprintln!("Coinbase reward must be >= {}, found {}", block_reward, coinbase_reward);
            return false;
        }

        // Ensure the block reward is not overpaid.
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
        preimage.extend_from_slice(&self.header.to_root()?.to_bytes_le()?);

        Ok(N::block_hash_crh().hash(&preimage)?)
    }

    /// Returns the commitments in the block, by constructing a flattened list of commitments from all transactions.
    fn to_commitments(&self) -> Result<Vec<Self::Commitment>> {
        self.transactions.to_commitments()
    }

    /// Returns the serial numbers in the block, by constructing a flattened list of serial numbers from all transactions.
    fn to_serial_numbers(&self) -> Result<Vec<Self::SerialNumber>> {
        self.transactions.to_serial_numbers()
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
        let genesis_block = Block::<Testnet2>::new_genesis(*account.address(), rng).unwrap();
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
            Testnet2::ALEO_STARTING_SUPPLY_IN_CREDITS
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
