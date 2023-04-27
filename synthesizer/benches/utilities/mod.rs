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

pub mod workload;
pub use workload::*;

use console::{
    account::{PrivateKey, ViewKey},
    network::{AleoID, Testnet3},
    prelude::Network,
    program::{Field, Group, Identifier, Literal, Plaintext, ProgramID, Record, Value, Zero, U64},
};
use snarkvm_synthesizer::{Block, Certificate, ConsensusMemory, ConsensusStore, Deployment, Fee, Header, Input, Metadata, Output, Owner, Program, Proof, Speculate, Transaction, Transactions, Transition, VerifyingKey, VM};
use snarkvm_utilities::{TestRng, ToBytes, Uniform};

use anyhow::Result;
use criterion::{BatchSize, Criterion};
use indexmap::IndexMap;
use itertools::Itertools;
use once_cell::sync::OnceCell;
use rand::{CryptoRng, Rng};
use std::{borrow::Borrow, fmt::Display, iter, str::FromStr};

/// A helper function to initialize a VM with a genesis block.
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
#[allow(unused)]
pub fn sample_next_block<R: Rng + CryptoRng>(
    vm: &VM<Testnet3, ConsensusMemory<Testnet3>>,
    private_key: &PrivateKey<Testnet3>,
    transactions: &[Transaction<Testnet3>],
    rng: &mut R,
) -> Result<Block<Testnet3>> {
    // Get the most recent block.
    let block_hash =
        vm.block_store().get_block_hash(*vm.block_store().heights().max().unwrap().borrow()).unwrap().unwrap();
    let previous_block = vm.block_store().get_block(&block_hash).unwrap().unwrap();

    // Construct the new block header.
    println!("Provided {} transactions", transactions.len());
    let transactions = Transactions::from(transactions);
    println!("Transactions object has {} transactions", transactions.len());
    println!("Found {} transaction ids", transactions.transaction_ids().collect_vec().len());
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

    // Construct the new block.
    println!("Creating block with {} transactions", transactions.len());
    Block::new(private_key, previous_block.hash(), header, transactions, None, rng)
}

/// A helper function that deploys and executes programs.
pub fn setup(
    vm: &VM<Testnet3, ConsensusMemory<Testnet3>>,
    private_key: &PrivateKey<Testnet3>,
    record: Record<Testnet3, Plaintext<Testnet3>>,
    batches: &[Vec<Operation<Testnet3>>],
    rng: &mut TestRng,
) -> Record<Testnet3, Plaintext<Testnet3>> {

    // For each set of operations in the batches, construct and add a block.
    for (i, operations) in batches.iter().enumerate() {
        println!("\nBatch: {}", i);
        // Storage for the transactions.
        let mut transactions = Vec::with_capacity(operations.len());
        // Construct transactions for the operations.
        for (i, operation) in operations.iter().enumerate() {
            match operation {
                Operation::Deploy(program) => {
                    // Construct dummy data for the deployment.
                    let id = <Testnet3 as Network>::TransitionID::from(Field::rand(rng));
                    let fee = construct_dummy_fee(rng);
                    // Construct dummy verifying keys.
                    let verifying_keys = program
                        .functions()
                        .iter()
                        .map(|(identifier, _)| {
                            (identifier.clone(), (VerifyingKey::mock(), Certificate::mock(identifier).unwrap()))
                        })
                        .collect_vec();
                    // Construct an unchecked deployment.
                    let deployment = Deployment::new_unchecked(Testnet3::EDITION, *program.clone(), verifying_keys);
                    // Construct a transaction for the deployment.
                    let transaction = Transaction::from_deployment_and_fee(&private_key, deployment, fee.clone(), rng).unwrap();
                    println!("Adding program: {}, fee id: {} txn id: {}", program.id(), fee.id(), transaction.id());
                    transactions.push(transaction);
                }
                Operation::Execute(program_id, function_name, inputs) => {
                    println!("Executing: {}::{}", program_id, function_name);
                    let authorization = vm.authorize(&private_key, program_id, function_name, inputs, rng).unwrap();
                    let (_, execution, _) = vm.execute(authorization, None, rng).unwrap();
                    transactions.push(Transaction::from_execution(execution, Some(construct_dummy_fee(rng))).unwrap());
                }
            }
        }
        // Create and add a block for the transactions, if any
        if !transactions.is_empty() {
            println!("Constructing block with {} transactions", transactions.len());
            let block = sample_next_block(vm, private_key, &transactions, rng).unwrap();
            vm.add_next_block(&block, None).unwrap();
        }
    }

    record
}

/// A helper function for benchmarking `Speculate::speculate`, `Speculate::commit`, and `VM::finalize`.
#[cfg(feature = "test-utilities")]
#[allow(unused)]
pub fn bench_speculate_commit_and_finalize(
    c: &mut Criterion,
    name: impl Display,
    vm: &VM<Testnet3, ConsensusMemory<Testnet3>>,
    private_key: &PrivateKey<Testnet3>,
    record: Option<Record<Testnet3, Plaintext<Testnet3>>>,
    deployments: &[Program<Testnet3>],
    executions: &[(String, String, Vec<Value<Testnet3>>)],
    rng: &mut TestRng,
) {
    let mut count = 0u64;
    let mut transactions = Vec::with_capacity(deployments.len() + executions.len());

    // Construct the deployment transactions.
    if !deployments.is_empty() {
        // Compute placeholder data for the deployment transactions.
        let id = <Testnet3 as Network>::TransactionID::default();
        let owner = Owner::new(private_key, id, rng).unwrap();
        let (_, fee, _) = vm
            .execute_fee(private_key, record.expect("Must supply a record, if benchmarking deployments."), 1, None, rng)
            .unwrap();

        for program in deployments {
            transactions.push(Transaction::from_deployment_unchecked(
                AleoID::from(Field::from_u64(count)),
                owner,
                Deployment::new_unchecked(<Testnet3 as Network>::EDITION, program.clone(), vec![]),
                fee.clone(),
            ));
            count += 1;
        }
    }

    // Construct the execution transactions.
    if !executions.is_empty() {
        for (program_id, function_name, inputs) in executions {
            let authorization = vm.authorize(private_key, program_id, function_name, inputs, rng).unwrap();
            let (_, execution, _) = vm.execute(authorization, None, rng).unwrap();
            transactions.push(Transaction::from_execution_unchecked(
                AleoID::from(Field::from_u64(count)),
                execution.clone(),
                None,
            ));
            count += 1;
        }
    }

    // Check that there is at least one transaction to benchmark.
    assert!(!transactions.is_empty(), "There must be at least one transaction to benchmark.");

    // Construct a `Speculate` object.
    let mut speculate = Speculate::new(vm.program_store().current_storage_root());

    // Benchmark speculation.
    c.bench_function(&format!("{}/speculate", name), |b| {
        b.iter_batched(
            || speculate.clone(),
            |mut speculate| {
                let accepted_transactions = speculate.speculate_transactions(vm, &transactions).unwrap();
                assert_eq!(transactions.len(), accepted_transactions.len());
            },
            BatchSize::SmallInput,
        )
    });

    // Speculate the transaction.
    speculate.speculate_transactions(vm, &transactions).unwrap();

    // Benchmark the commit operation.
    c.bench_function(&format!("{}/commit", name), |b| {
        b.iter_batched(|| speculate.clone(), |speculate| speculate.commit(vm).unwrap(), BatchSize::SmallInput)
    });

    // Construct a `Transactions` object.
    let transactions = Transactions::from(&transactions);

    // Benchmark the finalize operation.
    c.bench_function(&format!("{}/finalize", name), |b| b.iter(|| vm.finalize(&transactions, None).unwrap()));
}

/// A helper function for benchmarking the `VM::add_next_block` function.
#[allow(unused)]
pub fn bench_add_next_block(
    c: &mut Criterion,
    name: impl Display,
    vm: &VM<Testnet3, ConsensusMemory<Testnet3>>,
    private_key: &PrivateKey<Testnet3>,
    record: Option<Record<Testnet3, Plaintext<Testnet3>>>,
    deployments: &[Program<Testnet3>],
    executions: &[(String, String, Vec<Value<Testnet3>>)],
    rng: &mut TestRng,
) {
    let mut transactions = Vec::with_capacity(deployments.len());

    // The record used to source fees.
    let mut record = record;

    // Construct transactions for the deployments.
    for program in deployments.iter() {
        let program_size = program.to_bytes_le().unwrap().len();

        // Split out a fee record, updating VM state.
        let (fee_record, remaining_record) = split(
            vm,
            private_key,
            record.expect("Must provide a record, if benchmarking deployments"),
            program_size as u64,
            rng,
        );
        record = Some(remaining_record);

        transactions
            .push(Transaction::deploy(vm, private_key, program, (fee_record, program_size as u64), None, rng).unwrap());
    }

    // Construct the transactions for the executions.
    for (program_id, function_name, inputs) in executions.iter() {
        transactions.push(
            Transaction::execute(vm, private_key, (program_id, function_name), inputs.iter(), None, None, rng).unwrap(),
        );
    }

    // Check that there is at least one transaction to benchmark.
    assert!(!transactions.is_empty(), "There must be at least one transaction to benchmark.");

    // Benchmark the `add_next_block` function.
    c.bench_function(&format!("{}/add_next_block", name), |b| {
        b.iter_batched(
            || sample_next_block(vm, private_key, &transactions, rng).unwrap(),
            |block| vm.add_next_block(&block, None).unwrap(),
            BatchSize::PerIteration,
        )
    });
}

/// A helper function to invoke the `split` function an a credits.aleo record.
pub fn split(
    vm: &VM<Testnet3, ConsensusMemory<Testnet3>>,
    private_key: &PrivateKey<Testnet3>,
    record: Record<Testnet3, Plaintext<Testnet3>>,
    amount: u64,
    rng: &mut TestRng,
) -> (Record<Testnet3, Plaintext<Testnet3>>, Record<Testnet3, Plaintext<Testnet3>>) {
    let authorization = vm
        .authorize(
            private_key,
            "credits.aleo",
            "split",
            vec![Value::Record(record), Value::Plaintext(Plaintext::from(Literal::U64(U64::new(amount))))],
            rng,
        )
        .unwrap();
    let (response, execution, _) = vm.execute(authorization, None, rng).unwrap();

    // Create and add a block for the fee transaction.
    let block =
        sample_next_block(vm, private_key, &[Transaction::from_execution(execution, None).unwrap()], rng).unwrap();
    vm.add_next_block(&block, None).unwrap();

    match (response.outputs()[0].clone(), response.outputs()[1].clone()) {
        (Value::Record(fee_record), Value::Record(remaining_record)) => (fee_record, remaining_record),
        _ => unreachable!("`split` always returns a record"),
    }
}

pub fn sample_proof() -> Proof<Testnet3> {
    static INSTANCE: OnceCell<Proof<Testnet3>> = OnceCell::new();
    INSTANCE
        .get_or_init(|| {
            let rng = &mut TestRng::default();
            let private_key = PrivateKey::new(rng).unwrap();
            let (vm, record) = initialize_vm(&private_key, rng);
            // Sample a fee.
            let (_, fee, _) = vm.execute_fee(&private_key, record, 1u64, None, rng).unwrap();
            // Return the proof.
            fee.transition().proof().clone()
        })
        .clone()
}

#[cfg(feature = "test-utilities")]
pub fn construct_dummy_fee(rng: &mut TestRng) -> Fee<Testnet3> {
    let proof = sample_proof();
    Fee::from(
        Transition::new(
            ProgramID::from_str("credits.aleo").unwrap(),
            Identifier::from_str("fee").unwrap(),
            iter::repeat_with(|| Input::Private(Field::rand(rng), None)).take(Testnet3::MAX_INPUTS).collect_vec(),
            iter::repeat_with(|| Output::Private(Field::rand(rng), None)).take(Testnet3::MAX_OUTPUTS).collect_vec(),
            None,
            proof,
            console::types::Group::zero(),
            Field::zero(),
        ).unwrap(),
        <Testnet3 as Network>::StateRoot::default(),
        None,
    )
}
