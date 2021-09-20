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

use crate::{Network, Transaction, TransactionError, TransactionScheme};
use snarkvm_algorithms::merkle_tree::MerkleTree;
use snarkvm_utilities::{
    has_duplicates,
    to_bytes_le,
    variable_length_integer::{read_variable_length_integer, variable_length_integer},
    FromBytes,
    ToBytes,
};

use anyhow::Result;
use std::{
    io::{Read, Result as IoResult, Write},
    ops::{Deref, DerefMut},
    sync::Arc,
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct BlockTransactions<N: Network>(pub Vec<Transaction<N>>);

impl<N: Network> BlockTransactions<N> {
    /// Initializes an empty list of transactions.
    pub fn new() -> Self {
        Self(vec![])
    }

    /// Initializes from a given list of transactions.
    pub fn from(transactions: &[Transaction<N>]) -> Self {
        Self(transactions.to_vec())
    }

    /// Initializes an empty list of transactions.
    pub fn push(&mut self, transaction: Transaction<N>) {
        self.0.push(transaction);
    }

    /// Returns the transactions root, by computing the root for a Merkle tree of the transactions.
    pub fn to_transactions_root(&self) -> Result<N::TransactionsRoot> {
        assert!(!self.0.is_empty(), "Cannot process an empty list of transactions");
        let transaction_ids = (*self)
            .iter()
            .map(|tx| {
                let id_bytes = tx.to_transaction_id()?.to_bytes_le()?;
                assert_eq!(id_bytes.len(), 32);

                let mut transaction_id = [0u8; 32];
                transaction_id.copy_from_slice(&id_bytes);
                Ok(transaction_id)
            })
            .collect::<Result<Vec<[u8; 32]>>>()?;

        Ok(*MerkleTree::<N::TransactionsTreeParameters>::new(
            Arc::new(N::transactions_tree_parameters().clone()),
            &transaction_ids,
        )?
        .root())
    }

    /// Returns the commitments, by construction a flattened list of commitments from all transactions.
    pub fn to_commitments(&self) -> Result<Vec<<N as Network>::Commitment>> {
        assert!(!self.0.is_empty(), "Cannot process an empty list of transactions");
        Ok(self.0.iter().map(|tx| tx.commitments()).flatten().cloned().collect())
    }

    /// Returns the serial numbers, by construction a flattened list of serial numbers from all transactions.
    pub fn to_serial_numbers(&self) -> Result<Vec<<N as Network>::SerialNumber>> {
        assert!(!self.0.is_empty(), "Cannot process an empty list of transactions");
        Ok(self.0.iter().map(|tx| tx.serial_numbers()).flatten().cloned().collect())
    }

    /// Serializes the transactions into strings.
    pub fn serialize_as_str(&self) -> Result<Vec<String>, TransactionError> {
        self.0
            .iter()
            .map(|transaction| -> Result<String, TransactionError> { Ok(hex::encode(to_bytes_le![transaction]?)) })
            .collect::<Result<Vec<String>, TransactionError>>()
    }

    /// Returns `true` if there is a conflicting serial number or commitment in the transactions.
    #[deprecated]
    pub fn conflict_exists(&self) -> bool {
        let mut serial_numbers: Vec<N::SerialNumber> = vec![];
        let mut commitments: Vec<N::Commitment> = vec![];

        for tx in &self.0 {
            serial_numbers.extend(tx.serial_numbers());
            commitments.extend(tx.commitments());
        }

        // Check if the transactions in the block have duplicate serial numbers
        if has_duplicates(serial_numbers) {
            return true;
        }

        // Check if the transactions in the block have duplicate commitments
        if has_duplicates(commitments) {
            return true;
        }

        false
    }
}

impl<N: Network> FromBytes for BlockTransactions<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let num_transactions = read_variable_length_integer(&mut reader)?;
        let mut transactions = Vec::with_capacity(num_transactions);
        for _ in 0..num_transactions {
            transactions.push(FromBytes::read_le(&mut reader)?);
        }
        Ok(Self(transactions))
    }
}

impl<N: Network> ToBytes for BlockTransactions<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        variable_length_integer(self.0.len() as u64).write_le(&mut writer)?;
        for transaction in &self.0 {
            transaction.write_le(&mut writer)?;
        }
        Ok(())
    }
}

impl<N: Network> Default for BlockTransactions<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N: Network> Deref for BlockTransactions<N> {
    type Target = Vec<Transaction<N>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<N: Network> DerefMut for BlockTransactions<N> {
    fn deref_mut(&mut self) -> &mut Vec<Transaction<N>> {
        &mut self.0
    }
}
