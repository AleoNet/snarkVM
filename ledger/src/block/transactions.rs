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

use snarkvm_dpc::{TransactionError, TransactionScheme};
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
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Transactions<T: TransactionScheme>(pub Vec<T>);

impl<T: TransactionScheme> Transactions<T> {
    /// Initializes an empty list of transactions.
    pub fn new() -> Self {
        Self(vec![])
    }

    /// Initializes from a given list of transactions.
    pub fn from(transactions: &[T]) -> Self {
        Self(transactions.to_vec())
    }

    /// Initializes an empty list of transactions.
    pub fn push(&mut self, transaction: T) {
        self.0.push(transaction);
    }

    /// Returns the transaction ids.
    pub fn to_transaction_ids(&self) -> Result<Vec<[u8; 32]>> {
        self.0.iter().map(|tx| tx.transaction_id()).collect()
    }

    /// Serializes the transactions into strings.
    pub fn serialize_as_str(&self) -> Result<Vec<String>, TransactionError> {
        self.0
            .iter()
            .map(|transaction| -> Result<String, TransactionError> { Ok(hex::encode(to_bytes_le![transaction]?)) })
            .collect::<Result<Vec<String>, TransactionError>>()
    }

    /// Returns `true` if there is a conflicting serial number or commitment in the transactions.
    pub fn conflict_exists(&self) -> bool {
        let mut serial_numbers = vec![];
        let mut commitments = vec![];

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

impl<T: TransactionScheme> FromBytes for Transactions<T> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let num_transactions = read_variable_length_integer(&mut reader)?;
        let mut transactions = Vec::with_capacity(num_transactions);
        for _ in 0..num_transactions {
            let transaction: T = FromBytes::read_le(&mut reader)?;
            transactions.push(transaction);
        }
        Ok(Self(transactions))
    }
}

impl<T: TransactionScheme> ToBytes for Transactions<T> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        variable_length_integer(self.0.len() as u64).write_le(&mut writer)?;
        for transaction in &self.0 {
            transaction.write_le(&mut writer)?;
        }
        Ok(())
    }
}

impl<T: TransactionScheme> Default for Transactions<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: TransactionScheme> Deref for Transactions<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: TransactionScheme> DerefMut for Transactions<T> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        &mut self.0
    }
}
