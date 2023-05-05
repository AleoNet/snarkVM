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

#![allow(unused)]

use crate::utilities::{
    construct_next_block,
    initialize_object_store,
    initialize_vm,
    split,
    Benchmark,
    BenchmarkTransactions,
    ObjectStore,
    Operation,
};

use console::{
    network::Testnet3,
    prelude::Network,
    program::{Identifier, Literal, Value},
};
use snarkvm_synthesizer::{Block, ConsensusStorage, Program, Transaction, VM};

use console::{
    account::PrivateKey,
    program::{Plaintext, Record},
};

use anyhow::Result;
use console::{prelude::IoResult, program::Entry};
use itertools::Itertools;
use rand::Rng;
use snarkvm_synthesizer::helpers::memory::ConsensusMemory;
use snarkvm_utilities::{FromBytes, TestRng, ToBytes};
use std::{
    borrow::{Borrow, BorrowMut},
    collections::hash_map::DefaultHasher,
    hash::Hash,
    iter,
    path::{Path, PathBuf},
    str::FromStr,
};

/// A batch of benchmarks for the workload.
pub type BenchmarkBatch = Vec<(String, Vec<Transaction<Testnet3>>)>;

/// A `Workload` is a collection of benchmarks to be run together.
pub struct Workload {
    /// The name of the workload.
    name: String,
    /// The benchmarks to be run.
    benchmarks: Vec<Box<dyn Benchmark<Testnet3>>>,
    /// An object store to cache objects for the workload.
    object_store: ObjectStore,
}

impl Workload {
    /// Constructs a new workload.
    pub fn new(name: String, benchmarks: Vec<Box<dyn Benchmark<Testnet3>>>) -> Result<Self> {
        // Construct the path to a directory to store workload objects.
        let mut root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        root.push(".resources");
        root.push(&name);
        // Construct the object store.
        let object_store = ObjectStore::new(root)?;
        // Construct the workload.
        Ok(Self { name, benchmarks, object_store })
    }

    /// Adds a benchmark to the workload.
    pub fn add(&mut self, benchmark: Box<dyn Benchmark<Testnet3>>) {
        self.benchmarks.push(benchmark);
    }

    /// Returns the name of the workload.
    pub fn name(&self) -> &String {
        &self.name
    }

    /// Constructs batches of setup transactions and benchmark transactions from the benchmarks in the workload.
    /// Note that setup operations are aggregated across all benchmarks.
    pub fn setup<C: ConsensusStorage<Testnet3>>(
        &mut self,
    ) -> (VM<Testnet3, C>, PrivateKey<Testnet3>, BenchmarkBatch, TestRng) {
        // Check that the seed to the RNG is stored in the object store.
        let mut all_data_is_stored = self.object_store.contains("seed");
        println!("seed is stored: {}", all_data_is_stored);
        // Check that the relevant blocks are stored in the object store.
        println!("object_store contains num_blocks: {}", self.object_store.contains("num_blocks"));
        all_data_is_stored &= match self.object_store.get("num_blocks") {
            Err(err) => {
                println!("num_blocks is not stored: {:?}", err);
                false
            },
            Ok(num_blocks) => {
                let num_blocks: u64 = num_blocks;
                println!("num_blocks is stored: {}", num_blocks);
                (0..num_blocks).all(|i| self.object_store.contains(format!("block_{}", i)))
            }
        };
        println!("blocks are stored: {}", all_data_is_stored);
        // Check that the benchmark transactions are stored in the object store.
        for benchmark in &self.benchmarks {
            all_data_is_stored &= self.object_store.contains(benchmark.name())
        }
        println!("benchmarks are stored: {}", all_data_is_stored);

        // If all of the required items are not stored, clear the object store and initialize them.
        if !all_data_is_stored {
            let mut setup_operations = vec![];
            let mut benchmark_operations = vec![];

            // Collect the operations for each benchmark.
            for benchmark in &mut self.benchmarks {
                let setup_ops = benchmark.setup_operations();
                let benchmark_ops = benchmark.benchmark_operations();
                setup_operations.push(setup_ops);
                benchmark_operations.push((benchmark.name(), benchmark_ops));
            }

            // Fold the batches of setup operations across all benchmarks into a single sequence of batches.
            let max_num_batches = setup_operations.iter().map(|operations| operations.len()).max().unwrap_or(0);
            let mut aggregated_setup_operations = iter::repeat_with(Vec::new).take(max_num_batches).collect_vec();
            for setup_ops in setup_operations {
                for (i, operations) in setup_ops.into_iter().enumerate() {
                    aggregated_setup_operations[i].extend(operations);
                }
            }
            println!("\n\naggregated_setup_operations:");
            for (i, operations) in aggregated_setup_operations.iter().enumerate() {
                println!("  batch {}: {} operations", i, operations.len());
                for operation in operations {
                    match operation {
                        Operation::Deploy(program) => {
                            println!("    deploy program: {}", program.id())
                        }
                        Operation::Execute(program_name, function_name, inputs) => {
                            println!("    execute program: {}, function: {}", program_name, function_name)
                        }
                    }
                }
            }

            println!("\n\nbenchmark_operations:");
            for (name, operations) in benchmark_operations.iter() {
                println!("  benchmark: {}", name);
                for operation in operations {
                    match operation {
                        Operation::Deploy(program) => {
                            println!("    deploy program: {}", (**program).id())
                        }
                        Operation::Execute(program_name, function_name, inputs) => {
                            println!("    execute program: {}, function: {}", program_name, function_name)
                        }
                    }
                }
            }

            // Clear the object store.
            self.object_store.clear().unwrap();
            // Initialize the object store.
            initialize_object_store(&mut self.object_store, aggregated_setup_operations, benchmark_operations)
        } else {
            // Otherwise, load the items for the object store, initialize the VM, and return the VM, benchmark transactions, and rng.
            // Initialize the RNG.
            let mut rng = TestRng::fixed(self.object_store.get("seed").unwrap());

            // Sample the private key.
            let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();

            // Initialize the VM.
            let (vm, _) = initialize_vm::<C, _>(&private_key, &mut rng);

            println!("vm height: {:?}", vm.block_store().heights().collect_vec());

            // Load the blocks.
            let num_blocks: u64 = self.object_store.get("num_blocks").unwrap();
            let blocks: Vec<Block<Testnet3>> = (0..num_blocks).map(|i| self.object_store.get(&format!("block_{}", i)).unwrap()).collect_vec();

            println!("Collected {} blocks", blocks.len());

            // Print the heights of the blocks.
            for (i, block) in blocks.iter().enumerate() {
                println!("block {} height: {:?}", i, block.height());
            }

            // Add the blocks to the VM.
            for (i, block) in blocks.iter().enumerate() {
                println!("Adding block {} of {}", i, blocks.len());
                println!("  block height: {:?}", block.height());
                vm.add_next_block(block).unwrap();
            }

            // Load the benchmark transactions.
            let benchmark_transactions = self
                .benchmarks
                .iter()
                .map(|benchmark| {
                    let name = benchmark.name();
                    let transactions = self.object_store.get::<BenchmarkTransactions, _>(&name).unwrap().0;
                    (name, transactions)
                })
                .collect_vec();

            (vm, private_key, benchmark_transactions, rng)
        }
    }
}
