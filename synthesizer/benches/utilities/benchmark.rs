// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use crate::utilities::{initialize_vm, split, ObjectStore};

use console::{account::PrivateKey, network::Testnet3, prelude::Network, program::Value};
use snarkvm_synthesizer::{helpers::memory::ConsensusMemory, Program, Transaction};
use snarkvm_utilities::{FromBytes, TestRng, ToBytes};

use console::prelude::IoResult;
use std::{
    collections::hash_map::DefaultHasher,
    hash::Hash,
    io::{Read, Result, Write},
    iter,
    path::PathBuf,
};

/// An operation executed in a benchmark.
#[derive(Clone, Debug)]
#[allow(unused)]
pub enum Operation<N: Network> {
    /// Deploy a program.
    Deploy(Box<Program<N>>),
    /// Execute a program.
    Execute(String, String, Vec<Value<N>>),
}

/// A set of transactions to be run in a benchmark.
/// This is a wrapper around a vector of transactions, used to implement `FromBytes` and `ToBytes`.
pub struct BenchmarkTransactions(pub Vec<Transaction<Testnet3>>);

impl FromBytes for BenchmarkTransactions {
    fn read_le<R: Read>(mut reader: R) -> Result<Self>
    where
        Self: Sized,
    {
        // Read the number of transactions.
        let num_transactions = u64::read_le(&mut reader)? as usize;
        // Initialize the vector for the transactions.
        let mut transactions = Vec::with_capacity(num_transactions);
        // Read the transactions.
        for _ in 0..num_transactions {
            transactions.push(Transaction::read_le(&mut reader)?);
        }
        Ok(Self(transactions))
    }
}

impl ToBytes for BenchmarkTransactions {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()>
    where
        Self: Sized,
    {
        // Write the number of transactions.
        (self.0.len() as u64).write_le(&mut writer)?;
        // Write the transactions.
        self.0.iter().try_for_each(|transaction| transaction.write_le(&mut writer))
    }
}

/// A trait for benchmarks.
/// Note that `name` must be unique for each benchmark.
/// Note that `setup_operations` and `benchmark_operations` must be deterministic.
/// Note that each operation must be independent of the others.
pub trait Benchmark<N: Network> {
    /// The name of the benchmark.
    fn name(&self) -> String;
    /// Batches of operations to be run to setup the benchmark.
    fn setup_operations(&mut self) -> Vec<Vec<Operation<N>>>;
    /// Operations to be run for the benchmark.
    fn benchmark_operations(&mut self) -> Vec<Operation<N>>;
}
