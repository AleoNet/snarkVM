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

use crate::{AleoAmount, BlockError, Network, Transaction};
use snarkvm_algorithms::merkle_tree::*;
use snarkvm_utilities::{has_duplicates, to_bytes_le, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::{
    io::{Read, Result as IoResult, Write},
    ops::Deref,
    sync::Arc,
};

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Transactions<N: Network>(Vec<Transaction<N>>);

impl<N: Network> Transactions<N> {
    /// Initializes an empty transactions list.
    pub fn new() -> Self {
        Self(vec![])
    }

    /// Initializes from a given transactions list.
    pub fn from(transactions: &[Transaction<N>]) -> Result<Self> {
        let transactions = Self(transactions.to_vec());
        match transactions.is_valid() {
            true => Ok(transactions),
            false => Err(anyhow!("Failed to initialize the transactions list")),
        }
    }

    /// Adds the given transaction to the transactions list, if it is valid.
    pub fn add(&mut self, transaction: Transaction<N>) -> Result<()> {
        // Create a clone to test validity before appending.
        let mut transactions = self.clone();
        transactions.0.push(transaction);

        // Ensure the given transaction is valid in the transactions list.
        match transactions.is_valid() {
            true => Ok(*self = transactions),
            false => Err(anyhow!("Failed to initialize the transactions list")),
        }
    }

    /// Returns `true` if the transactions are well-formed.
    pub fn is_valid(&self) -> bool {
        // Ensure the transactions list is not empty.
        if self.0.len() == 0 {
            eprintln!("Cannot process validity checks on an empty transactions list");
            return false;
        }

        // Ensure each transaction is well-formed.
        if !self.0.as_parallel_slice().par_iter().all(Transaction::is_valid) {
            eprintln!("Invalid transaction found in the transactions list");
            return false;
        }

        // Ensure there are no duplicate serial numbers.
        if has_duplicates(self.0.iter().flat_map(Transaction::serial_numbers)) {
            eprintln!("Found duplicate serial numbers in the transactions list");
            return false;
        }

        // Ensure there are no duplicate commitments.
        if has_duplicates(self.0.iter().flat_map(Transaction::commitments)) {
            eprintln!("Found duplicate commitments in the transactions list");
            return false;
        }

        // Ensure there is 1 coinbase transaction.
        let num_coinbase = self.iter().filter(|t| t.value_balance().is_negative()).count();
        if num_coinbase != 1 {
            eprintln!("Block must have exactly 1 coinbase transaction, found {}", num_coinbase);
            return false;
        }

        true
    }

    /// Returns the transaction IDs, by constructing a flattened list of transaction IDs from all transactions.
    pub fn transaction_ids(&self) -> impl Iterator<Item = <N as Network>::TransactionID> + '_ {
        self.0.iter().map(Transaction::transaction_id)
    }

    /// Returns the transition IDs, by constructing a flattened list of transition IDs from all transactions.
    pub fn transition_ids(&self) -> impl Iterator<Item = <N as Network>::TransitionID> + '_ {
        self.0.iter().flat_map(Transaction::transition_ids)
    }

    /// Returns the ledger roots, by constructing a flattened list of ledger roots from all transactions.
    pub fn ledger_roots(&self) -> impl Iterator<Item = <N as Network>::LedgerRoot> + '_ {
        self.0.iter().map(Transaction::ledger_root)
    }

    /// Returns the serial numbers, by constructing a flattened list of serial numbers from all transactions.
    pub fn serial_numbers(&self) -> impl Iterator<Item = <N as Network>::SerialNumber> + '_ {
        self.0.iter().flat_map(Transaction::serial_numbers)
    }

    /// Returns the commitments, by constructing a flattened list of commitments from all transactions.
    pub fn commitments(&self) -> impl Iterator<Item = <N as Network>::Commitment> + '_ {
        self.0.iter().flat_map(Transaction::commitments)
    }

    /// Returns the transactions root, by computing the root for a Merkle tree of the transaction IDs.
    pub fn to_transactions_root(&self) -> Result<N::TransactionsRoot> {
        // TODO (howardwu): Optimize this design.
        match self.is_valid() {
            true => {
                let transaction_ids = (*self).iter().map(Transaction::transaction_id).collect::<Vec<_>>();
                let root = *MerkleTree::<N::TransactionsRootParameters>::new(
                    Arc::new(N::transactions_root_parameters().clone()),
                    &transaction_ids,
                )?
                .root();
                Ok(root.into())
            }
            false => Err(anyhow!("The transactions list is invalid")),
        }
    }

    /// Returns an inclusion proof for the transactions tree.
    pub fn to_transactions_inclusion_proof(
        &self,
        index: usize,
        leaf: impl ToBytes,
    ) -> Result<MerklePath<N::TransactionsRootParameters>> {
        // TODO (howardwu): Optimize this design.
        let transaction_ids = (*self).iter().map(Transaction::transaction_id).collect::<Vec<_>>();
        Ok(MerkleTree::<N::TransactionsRootParameters>::new(
            Arc::new(N::transactions_root_parameters().clone()),
            &transaction_ids,
        )?
        .generate_proof(index, &leaf)?)
    }

    /// Returns the total transaction fees, by summing the value balance from all positive transactions.
    /// Note - this amount does *not* include the block reward.
    pub fn to_transaction_fees(&self) -> Result<AleoAmount> {
        match self.is_valid() {
            true => self
                .0
                .iter()
                .filter_map(|t| match t.value_balance().is_negative() {
                    true => None,
                    false => Some(t.value_balance()),
                })
                .reduce(|a, b| a.add(b))
                .ok_or(anyhow!("Failed to compute the transaction fees for block")),
            false => Err(anyhow!("The transactions list is invalid")),
        }
    }

    /// Returns the net value balance, by summing the value balance from all transactions.
    pub fn to_net_value_balance(&self) -> Result<AleoAmount> {
        match self.is_valid() {
            true => Ok(self
                .0
                .iter()
                .map(Transaction::value_balance)
                .fold(AleoAmount::ZERO, |a, b| a.add(b))),
            false => Err(anyhow!("The transactions list is invalid")),
        }
    }

    /// Serializes the transactions into strings.
    pub fn serialize_as_str(&self) -> Result<Vec<String>> {
        match self.is_valid() {
            true => self
                .0
                .iter()
                .map(|transaction| -> Result<String> { Ok(hex::encode(to_bytes_le![transaction]?)) })
                .collect::<Result<Vec<String>>>(),
            false => Err(anyhow!("The transactions list is invalid").into()),
        }
    }
}

impl<N: Network> FromBytes for Transactions<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let num_transactions: u16 = FromBytes::read_le(&mut reader)?;
        let mut transactions = Vec::with_capacity(num_transactions as usize);
        for _ in 0..num_transactions {
            transactions.push(FromBytes::read_le(&mut reader)?);
        }

        // Ensure the transactions are well-formed.
        let transactions = Self(transactions);
        match transactions.is_valid() {
            true => Ok(transactions),
            false => Err(BlockError::Message("Invalid transactions list".to_string()).into()),
        }
    }
}

impl<N: Network> ToBytes for Transactions<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self.is_valid() {
            true => {
                (self.0.len() as u16).write_le(&mut writer)?;
                for transaction in &self.0 {
                    transaction.write_le(&mut writer)?;
                }
                Ok(())
            }
            false => Err(BlockError::Message("Invalid transactions list".to_string()).into()),
        }
    }
}

impl<N: Network> Default for Transactions<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N: Network> Deref for Transactions<N> {
    type Target = Vec<Transaction<N>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;

    #[test]
    fn test_duplicate_transactions() {
        // Fetch any transaction.
        let transaction = Testnet2::genesis_block().to_coinbase_transaction().unwrap();
        // Duplicate the transaction, and ensure it errors.
        assert!(Transactions::from(&[transaction.clone(), transaction]).is_err());
    }
}
