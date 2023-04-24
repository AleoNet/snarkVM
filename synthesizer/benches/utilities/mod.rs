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

use console::{
    account::{PrivateKey, ViewKey},
    network::{AleoID, Testnet3},
    prelude::Network,
    program::{Field, Identifier, Literal, Plaintext, ProgramID, Record, Value, Zero, U64},
};
use snarkvm_synthesizer::{
    Block,
    ConsensusMemory,
    ConsensusStore,
    Deployment,
    Header,
    Metadata,
    Owner,
    Program,
    Speculate,
    Transaction,
    Transactions,
    Transition,
    VM,
};
use snarkvm_utilities::{TestRng, ToBytes};

use anyhow::Result;
use criterion::{BatchSize, Criterion};
use indexmap::IndexMap;
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use std::{borrow::Borrow, fmt::Display};

pub fn initialize_vm<R: Rng + CryptoRng>(
    private_key: &PrivateKey<Testnet3>,
    rng: &mut R,
) -> (VM<Testnet3, ConsensusMemory<Testnet3>>, Record<Testnet3, Plaintext<Testnet3>>) {
    let vm = VM::from(ConsensusStore::open(None).unwrap()).unwrap();

    // Initialize the genesis block.
    let genesis = Block::genesis(&vm, private_key, rng).unwrap();

    // Fetch the unspent records.
    let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();

    // Select a record to spend.
    let view_key = ViewKey::try_from(private_key).unwrap();
    let record = records.values().next().unwrap().decrypt(&view_key).unwrap();

    // Update the VM.
    vm.add_next_block(&genesis, None).unwrap();

    (vm, record)
}

/// Construct a new block based on the given transactions.
#[cfg(feature = "test-utilities")]
#[allow(unused)]
pub fn sample_next_block<R: Rng + CryptoRng>(
    vm: &VM<Testnet3, ConsensusMemory<Testnet3>>,
    private_key: &PrivateKey<Testnet3>,
    transactions: &[Transaction<Testnet3>],
    previous_block: &Block<Testnet3>,
    rng: &mut R,
) -> Result<Block<Testnet3>> {
    // Construct the new block header.
    let transactions = Transactions::from(transactions);
    // Construct the metadata associated with the block.
    let metadata = Metadata::new(
        Testnet3::ID,
        previous_block.round() + 1,
        previous_block.height() + 1,
        Testnet3::STARTING_SUPPLY,
        0,
        Testnet3::GENESIS_COINBASE_TARGET,
        Testnet3::GENESIS_PROOF_TARGET,
        previous_block.last_coinbase_target(),
        previous_block.last_coinbase_timestamp(),
        Testnet3::GENESIS_TIMESTAMP + 1,
    )?;

    let header =
        Header::from(*vm.block_store().current_state_root(), transactions.to_root().unwrap(), Field::zero(), metadata)?;

    Block::new(private_key, previous_block.hash(), header, transactions, None, rng)
}

#[cfg(feature = "test-utilities")]
#[allow(unused)]
pub fn bench_speculate_and_commit(
    c: &mut Criterion,
    name: impl Display,
    initial_deployments: &[Program<Testnet3>],
    initial_executions: &[(ProgramID<Testnet3>, Identifier<Testnet3>, Vec<Value<Testnet3>>)],
    benchmark_deployments: &[Program<Testnet3>],
    benchmark_executions: &[(ProgramID<Testnet3>, Identifier<Testnet3>, Vec<Value<Testnet3>>)],
    runs: &[usize],
) {
    let rng = &mut TestRng::default();

    // Sample a new private key and address.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();

    // Initialize the VM.
    let (vm, record) = initialize_vm(&private_key, rng);
    let mut record = Value::Record(record);

    // Storage for the initial transactions.
    let mut init_deployment_transactions = Vec::with_capacity(initial_deployments.len());
    let mut init_execution_transactions = Vec::with_capacity(initial_executions.len());

    // Construct transactions for the initial deployments.
    for program in initial_deployments.iter() {
        let program_size = program.to_bytes_le().unwrap().len();
        let authorization = vm
            .authorize(
                &private_key,
                "credits.aleo",
                "split",
                vec![record, Value::Plaintext(Plaintext::from(Literal::U64(U64::new(program_size as u64))))],
                rng,
            )
            .unwrap();
        let (response, execution, _) = vm.execute(authorization, None, rng).unwrap();

        // Store the fee record.
        let fee_record = match response.outputs()[0].clone() {
            Value::Record(record) => record,
            _ => unreachable!("`split` always returns a record"),
        };
        // Extract the remaining record.
        record = response.outputs()[1].clone();

        // Create and add a block for the fee transaction.
        let transactions = vec![Transaction::from_execution(execution, None).unwrap()];
        let block_hash =
            vm.block_store().get_block_hash(*vm.block_store().heights().max().unwrap().borrow()).unwrap().unwrap();
        let previous_block = vm.block_store().get_block(&block_hash).unwrap().unwrap();
        let block = sample_next_block(&vm, &private_key, &transactions, &previous_block, rng).unwrap();
        vm.add_next_block(&block, None).unwrap();

        // Deploy the program.
        init_deployment_transactions.push(
            Transaction::deploy(&vm, &private_key, program, (fee_record, program_size as u64), None, rng).unwrap(),
        );
    }

    // Create and add a block for the initial deployment transactions, if any
    if !init_deployment_transactions.is_empty() {
        let block_hash =
            vm.block_store().get_block_hash(*vm.block_store().heights().max().unwrap().borrow()).unwrap().unwrap();
        let previous_block = vm.block_store().get_block(&block_hash).unwrap().unwrap();
        let block = sample_next_block(&vm, &private_key, &init_deployment_transactions, &previous_block, rng).unwrap();
        vm.add_next_block(&block, None).unwrap();
    }

    // Construct the transactions for the initial executions.
    for (program_id, function_name, inputs) in initial_executions.iter() {
        init_execution_transactions.push(
            Transaction::execute(&vm, &private_key, (program_id, function_name), inputs.iter(), None, None, rng)
                .unwrap(),
        );
    }

    // Construct and add the block for the initial execution transactions, if any
    if !init_execution_transactions.is_empty() {
        let block_hash =
            vm.block_store().get_block_hash(*vm.block_store().heights().max().unwrap().borrow()).unwrap().unwrap();
        let previous_block = vm.block_store().get_block(&block_hash).unwrap().unwrap();
        let block = sample_next_block(&vm, &private_key, &init_execution_transactions, &previous_block, rng).unwrap();
        vm.add_next_block(&block, None).unwrap();
    }

    // Run the deployment benchmarks for each of the runs.
    if !benchmark_deployments.is_empty() {
        // Compute placeholder data for the deployment transactions.
        let id = <Testnet3 as Network>::TransactionID::default();
        let owner = Owner::new(&private_key, id, rng).unwrap();
        let record = match record {
            Value::Record(record) => record,
            _ => unreachable!("`split` always returns a record"),
        };
        let (_, fee, _) = vm.execute_fee(&private_key, record, 1, None, rng).unwrap();

        for num_repetitions in runs {
            // Construct the required number of transactions.
            let mut count = 0u64;
            let mut transactions = vec![];
            for _ in 0..*num_repetitions {
                for program in benchmark_deployments {
                    transactions.push(Transaction::from_deployment_unchecked(
                        AleoID::from(Field::from_u64(count)),
                        owner,
                        Deployment::new_unchecked(<Testnet3 as Network>::EDITION, program.clone(), vec![]),
                        fee.clone(),
                    ));
                    count += 1;
                }
            }

            // Construct a `Speculate` object.
            let mut speculate = Speculate::new(vm.program_store().current_storage_root());

            // Benchmark speculation.
            c.bench_function(&format!("{}/deployment/{}_repetitions/speculate", name, num_repetitions), |b| {
                b.iter_batched(
                    || speculate.clone(),
                    |mut speculate| {
                        let accepted_transactions = speculate.speculate_transactions(&vm, &transactions).unwrap();
                        assert_eq!(transactions.len(), accepted_transactions.len());
                    },
                    BatchSize::SmallInput,
                )
            });

            // Speculate the transaction.
            speculate.speculate_transactions(&vm, &transactions).unwrap();

            // Benchmark the commit operation.
            c.bench_function(&format!("{}/deployment/{}_repetitions/commit", name, num_repetitions), |b| {
                b.iter_batched(|| speculate.clone(), |speculate| speculate.commit(&vm).unwrap(), BatchSize::SmallInput)
            });
        }
    }

    // Run the execution benchmarks for each of the runs.
    if !benchmark_executions.is_empty() {
        // Construct the executions.
        let executions = benchmark_executions
            .iter()
            .map(|(program_id, function_name, inputs)| {
                let authorization = vm.authorize(&private_key, program_id, function_name, inputs, rng).unwrap();
                let (_, execution, _) = vm.execute(authorization, None, rng).unwrap();
                execution
            })
            .collect_vec();

        for num_repetitions in runs {
            // Construct the required number of transactions.
            let mut count = 0u64;
            let mut transactions = vec![];
            for _ in 0..*num_repetitions {
                for execution in executions.iter() {
                    transactions.push(Transaction::from_execution_unchecked(
                        AleoID::from(Field::from_u64(count)),
                        execution.clone(),
                        None,
                    ));
                    count += 1;
                }
            }

            // Construct a `Speculate` object.
            let mut speculate = Speculate::new(vm.program_store().current_storage_root());

            // Benchmark speculation.
            c.bench_function(&format!("{}/execution/{}_repetitions/speculate", name, num_repetitions), |b| {
                b.iter_batched(
                    || speculate.clone(),
                    |mut speculate| {
                        let accepted_transactions = speculate.speculate_transactions(&vm, &transactions).unwrap();
                        assert_eq!(transactions.len(), accepted_transactions.len());
                    },
                    BatchSize::SmallInput,
                )
            });

            // Speculate the transaction.
            speculate.speculate_transactions(&vm, &transactions).unwrap();

            // Benchmark the commit operation.
            c.bench_function(&format!("{}/execution/{}_repetitions/commit", name, num_repetitions), |b| {
                b.iter_batched(|| speculate.clone(), |speculate| speculate.commit(&vm).unwrap(), BatchSize::SmallInput)
            });
        }
    }
}
