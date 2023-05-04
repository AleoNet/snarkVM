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

use crate::utilities::{Benchmark, initialize_vm, ObjectStore, split};

use console::{network::Testnet3, prelude::Network, program::Value};
use snarkvm_synthesizer::{Program, Transaction};

use itertools::Itertools;
use std::{collections::hash_map::DefaultHasher, hash::Hash, iter, path::PathBuf};
use console::account::PrivateKey;
use snarkvm_synthesizer::helpers::memory::ConsensusMemory;
use snarkvm_utilities::TestRng;

/// Batches of setup operations for the workload.
pub type SetupTransactions<N> = Vec<Vec<Transaction<N>>>;
/// Benchmark transactions for the workload.
pub type BenchmarkTransactions<N> = Vec<(String, Vec<Transaction<N>>)>;



/// A `Workload` is a collection of benchmarks to be run together.
struct Workload<N: Network> {
    /// The name of the workload.
    name: String,
    /// The benchmarks to be run.
    benchmarks: Vec<Box<dyn Benchmark<N>>>,
}

impl<N: Network> Workload<N> {
    /// Constructs a new workload.
    pub fn new(name: String, benchmarks: Vec<Box<dyn Benchmark<N>>>) -> Self {
        Self { name, benchmarks }
    }

    /// Returns the name of the workload.
    pub fn name(&self) -> &String {
        &self.name
    }


}

/// A helper function for preparing benchmarks.
/// This function takes a number of workloads and returns the setup operations and the benchmarks.
/// Note that setup operations are aggregated across all workloads.
pub fn prepare_benchmarks<N: Network>(
    workloads: Vec<Box<dyn Workload<N>>>,
) -> (SetupTransactions<N>, BenchmarkTransactions<N>) {
    let mut setup_transactions = vec![];
    let mut benchmarks = vec![];
    for mut workload in workloads {
        let (setup_operations, benchmark_operations) = workload.init();
        let mut object_store = ObjectStore::new(resources_directory(&workload.name())).unwrap();
        let transactions_are_stored = setup_operations.iter().flatten().chain(benchmark.iter()).all(|operation| {
            let uid = operation.uid();
            object_store.contains(&uid)
        });
        // If all transactions are not stored, clear the object store and initialize them
        if !transactions_are_stored {
            object_store.clear().unwrap();
            // Initialize the object store.
            initialize_object_store(setup_operations, benchmark, &mut object_store);
        }
        // For each setup operation, get its corresponding transaction.
        let setup = setup_operations
            .into_iter()
            .map(|operations| {
                operations
                    .into_iter()
                    .map(|operation| object_store.get::<Transaction<N>, _>(&operation.uid()).unwrap())
                    .collect_vec()
            })
            .collect_vec();
        // For each benchmark operation, get its corresponding transaction.
        let benchmark = benchmark_operations
            .into_iter()
            .map(|operation| object_store.get::<Transaction<N>, _>(&operation.uid()).unwrap())
            .collect_vec();

        setup_transactions.push(setup);
        benchmarks.push((workload.name(), benchmark));
    }

    // Aggregate the batches for each setup operation.
    let max_num_batches = setup_transactions.iter().map(|operations| operations.len()).max().unwrap_or(0);
    let mut batches = iter::repeat_with(Vec::new).take(max_num_batches).collect_vec();
    for setup in setup_transactions {
        for (i, batch) in setup.into_iter().enumerate() {
            batches[i].extend(batch);
        }
    }

    (batches, benchmarks)
}

/// A helper function to get the path to a resource directory for a workload.
pub fn resources_directory(name: &str) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push(".resources");
    path.push(name);
    path
}

/// A helper function to initialize an object store with transactions corresponding to a workload.
pub fn initialize_object_store(
    object_store: &mut ObjectStore,
    setup_operations: SetupOperations<Testnet3>,
    benchmark_operations: BenchmarkOperations<Testnet3>,
) {
    // Initialize the RNG.
    let rng = &mut TestRng::default();

    // Sample a new private key.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();

    // Initialize the VM.
    let (vm, mut record) = initialize_vm::<ConsensusMemory<Testnet3>, _>(&private_key, rng);

    // For each batch of setup operations, construct and add a block.
    for operations in setup_operations {
        // Storage for the transactions.
        let mut transactions = Vec::with_capacity(operations.len());
        // Construct transactions for the operations.
        for operation in operations {
            // Split out a record for the fee.

            match operation {
                Operation::Deploy(program) => {
                    // Construct a transaction for the deployment.
                    let transaction = Transaction::deploy(&vm, &private_key, )
                    transactions.push(mock_deployment_transaction(private_key, *program.clone(), rng));
                }
                Operation::Execute(program_id, function_name, inputs) => {
                    let transaction - Transaction::execute()
                    let authorization = vm.authorize(private_key, program_id, function_name, inputs, rng).unwrap();
                    let (_, execution, _) = vm.execute(authorization, None, rng).unwrap();
                    transactions.push(Transaction::from_execution(execution, Some(mock_fee(rng))).unwrap());
                }
            }
        }
        // Create and add a block for the transactions, if any
        if !transactions.is_empty() {
            let block = construct_next_block(vm, private_key, &transactions, rng).unwrap();
            vm.add_next_block(&block, None).unwrap();
        }
    }
}
