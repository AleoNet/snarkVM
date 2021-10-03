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

use crate::prelude::*;

use anyhow::{anyhow, Result};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub struct MemoryPool<N: Network> {
    transactions: HashMap<N::TransactionID, Transaction<N>>,
    serial_numbers: HashSet<N::SerialNumber>,
    commitments: HashSet<N::Commitment>,
}

impl<N: Network> MemoryPool<N> {
    /// Initializes a new instance of a memory pool.
    pub fn new() -> Self {
        Self {
            transactions: Default::default(),
            serial_numbers: Default::default(),
            commitments: Default::default(),
        }
    }

    /// Returns `true` if the given transaction exists in the memory pool.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> bool {
        match transaction.to_transaction_id() {
            Ok(id) => self.transactions.contains_key(&id),
            Err(error) => {
                eprintln!("Failed to lookup transaction ID: {}", error);
                return false;
            }
        }
    }

    /// Adds the given unconfirmed transaction to the memory pool.
    pub fn add(&mut self, transaction: &Transaction<N>) -> Result<()> {
        // Ensure the unconfirmed transaction itself is valid.
        if !transaction.is_valid() {
            return Err(anyhow!("The unconfirmed transaction is invalid"));
        }

        // Ensure the transaction does not already exist in the memory pool.
        let transaction_id = transaction.to_transaction_id()?;
        if self.transactions.contains_key(&transaction_id) {
            return Err(anyhow!("Transaction already exists in memory pool"));
        }

        // Ensure the memory pool does not already contain a given serial numbers.
        let serial_numbers = transaction.serial_numbers();
        for serial_number in serial_numbers {
            if self.serial_numbers.contains(serial_number) {
                return Err(anyhow!("Serial number already used in memory pool"));
            }
        }

        // Ensure the memory pool does not already contain a given commitments.
        let commitments = transaction.commitments();
        for commitment in commitments {
            if self.commitments.contains(commitment) {
                return Err(anyhow!("Commitment already used in memory pool"));
            }
        }

        // Add the transaction to the memory pool. This code section executes atomically.
        {
            let mut memory_pool = self.clone();

            memory_pool.transactions.insert(transaction_id, transaction.clone());
            for serial_number in serial_numbers {
                memory_pool.serial_numbers.insert(*serial_number);
            }
            for commitment in commitments {
                memory_pool.commitments.insert(*commitment);
            }

            *self = memory_pool;
        }

        Ok(())
    }
}
