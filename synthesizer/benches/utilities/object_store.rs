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

use snarkvm_utilities::{FromBytes, TestRng, ToBytes};

use crate::utilities::{construct_next_block, initialize_vm, split, BenchmarkBatch, BenchmarkTransactions, Operation};
use anyhow::{bail, Result};
use console::{
    account::PrivateKey,
    network::Testnet3,
    program::{Entry, Identifier, Literal, Plaintext, Record},
};
use itertools::Itertools;
use rand::Rng;
use snarkvm_synthesizer::{ConsensusStorage, Transaction, VM};
use std::{
    path::{Path, PathBuf},
    str::FromStr,
};

pub struct ObjectStore {
    root: PathBuf,
    keys: Vec<PathBuf>,
}

impl ObjectStore {
    pub fn new(root: PathBuf) -> Result<Self> {
        // Create the root directory if it does not exist.
        if !root.try_exists()? {
            std::fs::create_dir_all(&root)?;
        }
        Ok(Self { root, keys: Vec::new() })
    }

    pub fn keys(&self) -> impl Iterator<Item = &PathBuf> {
        self.keys.iter()
    }

    pub fn get<O: FromBytes, P: AsRef<Path>>(&mut self, path: P) -> Result<O> {
        let full_path = self.root.join(path);
        let bytes = std::fs::read(full_path)?;
        O::from_bytes_le(&bytes)
    }

    pub fn insert<O: ToBytes, P: AsRef<Path>>(&mut self, path: P, object: &O) -> Result<()> {
        let full_path = self.root.join(path);
        if !full_path.parent().expect("parent directory exists").exists() {
            std::fs::create_dir_all(full_path.parent().expect("parent directory exists"))?;
        }
        let bytes = object.to_bytes_le()?;
        std::fs::write(&full_path, bytes)?;
        self.keys.push(full_path);
        Ok(())
    }

    pub fn contains<P: AsRef<Path>>(&self, path: P) -> bool {
        self.root.join(path).exists()
    }

    pub fn clear(&mut self) -> Result<()> {
        for key in self.keys() {
            std::fs::remove_file(key)?;
        }
        self.keys.clear();
        Ok(())
    }
}

/// A helper function to initialize an object store with transactions corresponding to a workload.
pub fn initialize_object_store<C: ConsensusStorage<Testnet3>>(
    object_store: &mut ObjectStore,
    setup_operations: Vec<Vec<Operation<Testnet3>>>,
    benchmark_operations: Vec<(String, Vec<Operation<Testnet3>>)>,
) -> (VM<Testnet3, C>, PrivateKey<Testnet3>, BenchmarkBatch, TestRng) {
    println!("Initializing object store...");

    // Select a random seed for the RNG.
    // Store the seed in the object store.
    let seed: u64 = rand::thread_rng().gen();
    object_store.insert("seed", &seed).unwrap();

    println!("Stored the seed in the object store.");

    // Initialize the RNG.
    let mut rng = TestRng::fixed(seed);

    // Sample a new private key.
    let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();

    // Initialize the VM.
    let (vm, record) = initialize_vm::<C, _>(&private_key, &mut rng);

    println!("Initialized the VM.");

    // Calculate the number of fee records needed for the workload.
    let num_fee_records = setup_operations.iter().flatten().count() + benchmark_operations.len();
    let num_levels_of_splits = num_fee_records.next_power_of_two().ilog2();

    // Helper function to get the balance of a `credits.aleo` record.
    let get_balance = |record: &Record<Testnet3, Plaintext<Testnet3>>| -> u64 {
        match record.data().get(&Identifier::from_str("microcredits").unwrap()).unwrap() {
            Entry::Private(Plaintext::Literal(Literal::U64(amount), ..)) => **amount,
            _ => unreachable!("Invalid entry type for credits.aleo."),
        }
    };

    // Initialize a counter for each block added to the VM.
    let mut block_counter = 0;

    println!("Splitting the initial fee record into {} fee records.", num_fee_records);

    // Construct fee records for the workload, storing the relevant data in the object store.
    let balance = get_balance(&record);
    let mut fee_records = vec![(record, balance)];
    let mut fee_counter = 1;
    for _ in 0..num_levels_of_splits {
        let mut transactions = Vec::with_capacity(fee_records.len());
        for (fee_record, balance) in fee_records.drain(..).collect_vec() {
            if fee_counter < num_fee_records {
                println!("Splitting out the {}-th record of size {}.", fee_counter, balance / 2);
                let (first, second, fee_transaction) = split(&vm, &private_key, fee_record, balance / 2, &mut rng);
                let balance = get_balance(&first);
                fee_records.push((first, balance));
                let balance = get_balance(&second);
                fee_records.push((second, balance));
                transactions.push(fee_transaction);
                fee_counter += 1;
            } else {
                fee_records.push((fee_record, balance));
            }
        }
        // Create a block for the fee transactions and add them to the VM.
        let block = construct_next_block(&vm, &private_key, &transactions, &mut rng).unwrap();
        object_store.insert(format!("block_{}", block_counter), &block).unwrap();
        vm.add_next_block(&block).unwrap();
        block_counter += 1;
    }

    // Store the number of blocks in the object store.
    object_store.insert("num_blocks", &block_counter).unwrap();

    println!("Constructed fee records for the workload.");

    // A helper to construct transactions from an operation.
    let mut construct_transaction = |operation: &Operation<Testnet3>, rng: &mut TestRng| {
        match &operation {
            Operation::Deploy(program) => {
                println!("Deploying program: {}", (**program).id());
                // Construct a transaction for the deployment.
                Transaction::deploy(
                    &vm,
                    &private_key,
                    &**program,
                    fee_records.pop().expect("Not enough fee records provided."),
                    None,
                    rng,
                )
            }
            Operation::Execute(program_id, function_name, inputs) => {
                println!("Executing function: {}.{}", program_id, function_name);
                // Construct a transaction for the execution.
                Transaction::execute(
                    &vm,
                    &private_key,
                    (program_id, function_name),
                    inputs.iter(),
                    Some(fee_records.pop().expect("Not enough fee records provided.")),
                    None,
                    rng,
                )
            }
        }
    };

    // For each batch of setup operations, construct and add a block.
    for operations in setup_operations {
        // Storage for the transactions.
        let mut transactions = Vec::with_capacity(operations.len());
        // Construct transactions for the operations.
        for operation in &operations {
            let transaction = construct_transaction(operation, &mut rng).unwrap();
            transactions.push(transaction);
        }
        // Create and add a block for the transactions, if any
        if !transactions.is_empty() {
            let block = construct_next_block(&vm, &private_key, &transactions, &mut rng).unwrap();
            object_store.insert(format!("block_{}", block_counter), &block).unwrap();
            vm.add_next_block(&block).unwrap();
            block_counter += 1;
        }
    }

    println!("Constructed and added blocks for the setup operations.");

    // For each set of benchmark operations, construct the corresponding transactions.
    let mut benchmark_transactions = Vec::with_capacity(benchmark_operations.len());
    for (name, operations) in benchmark_operations {
        let mut transactions = Vec::with_capacity(operations.len());
        for operation in &operations {
            let transaction = construct_transaction(operation, &mut rng).unwrap();
            transactions.push(transaction);
        }
        let object = BenchmarkTransactions(transactions);
        object_store.insert(name.clone(), &object).unwrap();
        benchmark_transactions.push((name.clone(), object.0));
    }

    println!("Constructed transactions for the benchmark operations.");

    (vm, private_key, benchmark_transactions, rng)
}
