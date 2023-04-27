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

#![cfg(feature = "test-utilities")]

#[macro_use]
extern crate criterion;

mod utilities;

use std::iter;
use utilities::*;

mod workloads;
use workloads::*;

use console::{
    account::PrivateKey,
    network::{AleoID, Testnet3},
    prelude::Network,
    types::Field,
};
use snarkvm_synthesizer::{Deployment, Owner, Speculate, Transaction};
use snarkvm_utilities::TestRng;

use criterion::{BatchSize, Criterion};
use itertools::Itertools;

// Note: The number of commands that can be included in a finalize block must be within the range [1, 255].
const NUM_COMMANDS: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128, 255];
const NUM_EXECUTIONS: &[usize] = &[2, 4, 8, 16, 32, 64, 128, 256];
const NUM_PROGRAMS: &[usize] = &[2, 4, 8, 16, 32, 64, 128, 255];

/// A helper function for benchmarking `Speculate::speculate`.
#[cfg(feature = "test-utilities")]
#[allow(unused)]
pub fn bench_speculate(c: &mut Criterion, workloads: &[Box<dyn Workload<Testnet3>>]) {
    // Initialize the RNG.
    let rng = &mut TestRng::default();

    // Sample a new private key.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();

    // Initialize the VM.
    let (vm, record) = initialize_vm(&private_key, rng);

    // Get the setup operations.
    let setup_operations = workloads.iter().map(|workload| workload.setup()).collect_vec();

    // Aggregate the batches for each setup operation.
    let max_num_batches = setup_operations.iter().map(|operations| operations.len()).max().unwrap_or(0);
    let mut batches = iter::repeat_with(|| vec![]).take(max_num_batches).collect_vec();
    for setup in setup_operations {
        for (i, batch) in setup.into_iter().enumerate() {
            batches[i].extend(batch);
        }
    }

    // Deploy and execute programs to get the VM in the desired state.
    let mut record = setup(&vm, &private_key, record, &batches, rng);

    // For each workload, get the name.
    let benchmark_names = workloads.iter().map(|workload| workload.name()).collect_vec();

    // For each workload, generate the benchmark operations.
    let benchmark_operations = workloads.iter().map(|workload| workload.run()).collect_vec();

    // Benchmark each of the programs.
    let mut count = 0;
    for (name, operations) in benchmark_names.into_iter().zip_eq(benchmark_operations.into_iter()) {
        // // Split out a record for the benchmark.
        // let (remaining_record, fee_record) = split(&vm, &private_key, record, 1, rng);
        // record = remaining_record;

        assert!(!operations.is_empty(), "There must be at least one operation to benchmark.");

        // // Construct mock data for the transactions.
        // let id = <Testnet3 as Network>::TransactionID::default();
        // let owner = Owner::new(&private_key, id, rng).unwrap();
        // let (_, fee, _) = vm.execute_fee(&private_key, fee_record, 1, None, rng).unwrap();

        // Construct the transactions.
        println!("Benchmark #{}: {} transactions", count, operations.len());
        let mut transactions = Vec::with_capacity(operations.len());
        for (i, operation) in operations.iter().enumerate() {
            match operation {
                Operation::Deploy(program) => {
                    // transactions.push(Transaction::from_deployment_unchecked(
                    //     AleoID::from(Field::from_u64(i as u64)),
                    //     owner,
                    //     Deployment::new_unchecked(<Testnet3 as Network>::EDITION, *program.clone(), vec![]),
                    //     fee.clone(),
                    // ));
                }
                Operation::Execute(program_id, function_name, inputs) => {
                    let authorization = vm.authorize(&private_key, program_id, function_name, inputs, rng).unwrap();
                    let (_, execution, _) = vm.execute(authorization, None, rng).unwrap();
                    let transaction = Transaction::from_execution(execution, Some(construct_dummy_fee(rng))).unwrap();
                    transactions.push(transaction)
                }
            }
        }

        // Construct a `Speculate` object.
        let mut speculate = Speculate::new(vm.program_store().current_storage_root());

        // Benchmark speculation.
        c.bench_function(&format!("{}/speculate", name), |b| {
            b.iter_batched(
                || speculate.clone(),
                |mut speculate| {
                    let accepted_transactions = speculate.speculate_transactions(&vm, &transactions).unwrap();
                    assert_eq!(transactions.len(), accepted_transactions.len());
                },
                BatchSize::SmallInput,
            )
        });
    }
}

fn bench_one_operation(c: &mut Criterion) {
    // Initialize the workloads.
    let mut workloads: Vec<Box<dyn Workload<Testnet3>>> = vec![];
    workloads.extend(NUM_COMMANDS.iter().map(|num_commands| Box::new(StaticGet::new(1, *num_commands, 1, 1)) as Box<dyn Workload<Testnet3>>));
    workloads.extend(NUM_COMMANDS.iter().map(|num_commands| Box::new(StaticGetOrInit::new(1, *num_commands, 1, 1)) as Box<dyn Workload<Testnet3>>));
    workloads.extend(NUM_COMMANDS.iter().map(|num_commands| Box::new(StaticSet::new(1, *num_commands, 1, 1)) as Box<dyn Workload<Testnet3>>));
    //workloads.push(Box::new(StaticGet::new(1, 1, 1, 1)) as Box<dyn Workload<Testnet3>>);

    bench_speculate(c, &workloads)
}

fn bench_multiple_operations(c: &mut Criterion) {
    println!("Hello");
    // Initialize the workloads.
    let mut workloads: Vec<Box<dyn Workload<Testnet3>>> = vec![];
    let max_commands = *NUM_COMMANDS.last().unwrap();
    //workloads.extend(NUM_EXECUTIONS.iter().map(|num_executions| Box::new(StaticGet::new(1, max_commands, *num_executions, 1)) as Box<dyn Workload<Testnet3>>));
    workloads.extend(NUM_EXECUTIONS.iter().map(|num_executions| {
        Box::new(StaticGetOrInit::new(1, max_commands, *num_executions, 1)) as Box<dyn Workload<Testnet3>>
    }));
    workloads.extend(NUM_EXECUTIONS.iter().map(|num_executions| {
        Box::new(StaticSet::new(1, max_commands, *num_executions, 1)) as Box<dyn Workload<Testnet3>>
    }));

    bench_speculate(c, &workloads)
}

fn bench_multiple_operations_with_multiple_programs(c: &mut Criterion) {
    // Initialize the workloads.
    let max_commands = *NUM_COMMANDS.last().unwrap();
    let max_executions = *NUM_EXECUTIONS.last().unwrap();
    let mut workloads: Vec<Box<dyn Workload<Testnet3>>> = vec![];
    workloads.extend(NUM_PROGRAMS.iter().map(|num_programs| {
        Box::new(StaticGet::new(1, max_commands, max_executions, *num_programs)) as Box<dyn Workload<Testnet3>>
    }));
    workloads.extend(NUM_PROGRAMS.iter().map(|num_programs| {
        Box::new(StaticGetOrInit::new(1, max_commands, max_executions, *num_programs)) as Box<dyn Workload<Testnet3>>
    }));
    workloads.extend(NUM_PROGRAMS.iter().map(|num_programs| {
        Box::new(StaticSet::new(1, max_commands, max_executions, *num_programs)) as Box<dyn Workload<Testnet3>>
    }));

    bench_speculate(c, &workloads)
}

criterion_group! {
    name = benchmarks;
    config = Criterion::default().sample_size(10);
    targets = bench_one_operation, bench_multiple_operations,
}
criterion_group! {
    name = long_benchmarks;
    config = Criterion::default().sample_size(10);
    targets = bench_multiple_operations_with_multiple_programs
}
#[cfg(all(feature = "test-utilities", feature = "long-benchmarks"))]
criterion_main!(long_benchmarks);
#[cfg(all(feature = "test-utilities", not(any(feature = "long-benchmarks"))))]
criterion_main!(benchmarks);
