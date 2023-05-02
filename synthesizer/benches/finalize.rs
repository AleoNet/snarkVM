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
use utilities::*;

mod workloads;
use workloads::*;

use console::{account::PrivateKey, network::Testnet3};
use snarkvm_synthesizer::{Transaction, Transactions};
use snarkvm_utilities::TestRng;

use criterion::{BatchSize, Criterion};
use snarkvm_synthesizer::helpers::memory::ConsensusMemory;

// Note: The number of commands that can be included in a finalize block must be within the range [1, 255].
const NUM_COMMANDS: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128, 255];
const NUM_EXECUTIONS: &[usize] = &[2, 4, 8, 16, 32, 64];
const NUM_PROGRAMS: &[usize] = &[2, 4, 8, 16, 32, 64];

/// A helper function for benchmarking `VM::finalize`.
#[cfg(feature = "test-utilities")]
#[allow(unused)]
pub fn bench_finalize(c: &mut Criterion, workloads: Vec<Box<dyn Workload<Testnet3>>>) {
    // Initialize the RNG.
    let rng = &mut TestRng::default();

    // Sample a new private key.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();

    // Initialize the VM.
    let (vm, record) = initialize_vm::<ConsensusMemory<Testnet3>, _>(&private_key, rng);

    // Prepare the benchmarks.
    let (setup_operations, benchmarks) = prepare_benchmarks(workloads);

    // Deploy and execute programs to get the VM in the desired state.
    setup(&vm, &private_key, &setup_operations, rng);

    // Benchmark each of the programs.
    for (name, operations) in benchmarks {
        assert!(!operations.is_empty(), "There must be at least one operation to benchmark.");

        // Construct the transactions.
        let mut transactions = Vec::with_capacity(operations.len());
        for operation in operations.iter() {
            match operation {
                Operation::Deploy(program) => {
                    // Construct a transaction for the deployment.
                    transactions.push(mock_deployment_transaction(&private_key, *program.clone(), rng));
                }
                Operation::Execute(program_id, function_name, inputs) => {
                    let authorization = vm.authorize(&private_key, program_id, function_name, inputs, rng).unwrap();
                    let (_, execution, _) = vm.execute(authorization, None, rng).unwrap();
                    let transaction = Transaction::from_execution(execution, Some(mock_fee(rng))).unwrap();
                    transactions.push(transaction)
                }
            }
        }

        // Construct a `Transactions` object.
        let transactions = Transactions::from(&transactions);

        // Benchmark speculation.
        c.bench_function(&format!("{}/finalize", name), |b| {
            b.iter_batched(|| {}, |speculate| vm.finalize(&transactions, None).unwrap(), BatchSize::SmallInput)
        });
    }
}

fn bench_one_operation(c: &mut Criterion) {
    // Initialize the workloads.
    let mut workloads: Vec<Box<dyn Workload<Testnet3>>> = vec![];
    for num_commands in NUM_COMMANDS {
        //workloads.push(Box::new(StaticGet::new(1, *num_commands, 1, 1) as Box<dyn Workload<Testnet3>>));
        // workloads.push(Box::new(StaticGetOrInit::new(1, *num_commands, 1, 1)) as Box<dyn Workload<Testnet3>>);
        // workloads.push(Box::new(StaticSet::new(1, *num_commands, 1, 1)) as Box<dyn Workload<Testnet3>>);
    }
    workloads.push(Box::new(MintPublic::new(1)) as Box<dyn Workload<Testnet3>>);
    workloads.push(Box::new(TransferPrivateToPublic::new(1)) as Box<dyn Workload<Testnet3>>);
    workloads.push(Box::new(TransferPublic::new(1)) as Box<dyn Workload<Testnet3>>);
    workloads.push(Box::new(TransferPublicToPrivate::new(1)) as Box<dyn Workload<Testnet3>>);

    bench_finalize(c, workloads)
}

fn bench_multiple_operations(c: &mut Criterion) {
    // Initialize the workloads.
    let mut workloads: Vec<Box<dyn Workload<Testnet3>>> = vec![];
    let max_commands = *NUM_COMMANDS.last().unwrap();
    for num_executions in NUM_EXECUTIONS {
        //workloads.push(Box::new(StaticGet::new(1, max_commands, *num_executions, 1) as Box<dyn Workload<Testnet3>>));
        // workloads
        //     .push(Box::new(StaticGetOrInit::new(1, max_commands, *num_executions, 1)) as Box<dyn Workload<Testnet3>>);
        // workloads.push(Box::new(StaticSet::new(1, max_commands, *num_executions, 1)) as Box<dyn Workload<Testnet3>>);
        workloads.push(Box::new(MintPublic::new(*num_executions)) as Box<dyn Workload<Testnet3>>);
        workloads.push(Box::new(TransferPrivateToPublic::new(*num_executions)) as Box<dyn Workload<Testnet3>>);
        workloads.push(Box::new(TransferPublic::new(*num_executions)) as Box<dyn Workload<Testnet3>>);
        workloads.push(Box::new(TransferPublicToPrivate::new(*num_executions)) as Box<dyn Workload<Testnet3>>);
    }

    bench_finalize(c, workloads)
}

fn bench_multiple_operations_with_multiple_programs(c: &mut Criterion) {
    // Initialize the workloads.
    let max_commands = *NUM_COMMANDS.last().unwrap();
    let max_executions = *NUM_EXECUTIONS.last().unwrap();
    let mut workloads: Vec<Box<dyn Workload<Testnet3>>> = vec![];
    for num_programs in NUM_PROGRAMS {
        //workloads.push(Box::new(StaticGet::new(1, max_commands, max_executions, *num_programs) as Box<dyn Workload<Testnet3>>));
        workloads.push(Box::new(StaticGetOrInit::new(1, max_commands, max_executions, *num_programs))
            as Box<dyn Workload<Testnet3>>);
        workloads.push(
            Box::new(StaticSet::new(1, max_commands, max_executions, *num_programs)) as Box<dyn Workload<Testnet3>>
        );
    }

    bench_finalize(c, workloads)
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
