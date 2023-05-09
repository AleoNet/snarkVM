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

#![cfg(feature = "testing")]

#[macro_use]
extern crate criterion;

mod benchmarks;
use benchmarks::*;

mod utilities;
use utilities::*;

use console::network::Testnet3;
use snarkvm_synthesizer::ConsensusStorage;

use criterion::{BatchSize, Criterion};
use std::fmt::Display;

// Note: The number of commands that can be included in a finalize block must be within the range [1, 255].
const NUM_COMMANDS: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128, 255];
const NUM_EXECUTIONS: &[usize] = &[2, 4, 8, 16, 32, 64];
const NUM_PROGRAMS: &[usize] = &[2, 4, 8, 16, 32, 64];

/// A helper function for benchmarking `VM::add_next_block`.
#[cfg(feature = "testing")]
#[allow(unused)]
pub fn bench_add_next_block<C: ConsensusStorage<Testnet3>>(
    c: &mut Criterion,
    header: impl Display,
    mut workload: Workload,
) {
    // Setup the workload.
    let (vm, private_key, benchmark_transactions, mut rng) = workload.setup::<C>();

    // Run the benchmarks
    for (name, transactions) in benchmark_transactions {
        if transactions.is_empty() {
            println!("Skipping benchmark {} because it has no transactions.", name);
            continue;
        }

        let mut num_transactions = 0f64;
        let mut num_rejected = 0f64;

        c.bench_function(&format!("{header}/{name}/add_next_block"), |b| {
            b.iter_batched(
                // TODO: Do the blocks need to be removed on each iteration?
                || {
                    let block = construct_next_block(&vm, &private_key, &transactions, &mut rng).unwrap();
                    num_transactions += block.transactions().iter().count() as f64;
                    num_rejected += block.transactions().iter().filter(|t| t.is_rejected()).count() as f64;
                    block
                },
                |block| {
                    vm.add_next_block(&block).unwrap();
                },
                BatchSize::PerIteration,
            )
        });
        println!(
            "| {header}/{name}/add_next_block | Transactions: {} | Rejected: {} | Percent Rejected: {}",
            num_transactions,
            num_rejected,
            (num_rejected / num_transactions) * 100.0
        );
    }
}

fn bench_one_operation(c: &mut Criterion) {
    // Initialize the workload.
    let workload = one_execution_workload(NUM_COMMANDS);

    #[cfg(not(any(feature = "rocks")))]
    bench_add_next_block::<ConsensusMemory<Testnet3>>(c, "memory", workload);
    #[cfg(any(feature = "rocks"))]
    bench_add_next_block::<snarkvm_synthesizer::helpers::rocksdb::ConsensusDB<Testnet3>>(c, "db", workload);
}

fn bench_multiple_operations(c: &mut Criterion) {
    // Initialize the workload.
    let workload = multiple_executions_workload(NUM_EXECUTIONS, *NUM_COMMANDS.last().unwrap());

    #[cfg(not(any(feature = "rocks")))]
    bench_add_next_block::<ConsensusMemory<Testnet3>>(c, "memory", workload);
    #[cfg(any(feature = "rocks"))]
    bench_add_next_block::<snarkvm_synthesizer::helpers::rocksdb::ConsensusDB<Testnet3>>(c, "db", workload);
}

fn bench_multiple_operations_with_multiple_programs(c: &mut Criterion) {
    // Initialize the workload.
    let workload = multiple_executions_multiple_programs_workload(
        NUM_PROGRAMS,
        *NUM_COMMANDS.last().unwrap(),
        *NUM_EXECUTIONS.last().unwrap(),
    );

    #[cfg(not(any(feature = "rocks")))]
    bench_add_next_block::<ConsensusMemory<Testnet3>>(c, "memory", workload);
    #[cfg(any(feature = "rocks"))]
    bench_add_next_block::<snarkvm_synthesizer::helpers::rocksdb::ConsensusDB<Testnet3>>(c, "db", workload);
}

criterion_group! {
    name = benchmarks;
    config = Criterion::default().sample_size(10);
    //targets = bench_single_deployment, bench_one_operation, bench_multiple_deployments, bench_multiple_operations
    targets = bench_one_operation, bench_multiple_operations
}
criterion_group! {
    name = long_benchmarks;
    config = Criterion::default().sample_size(10);
    targets = bench_multiple_operations_with_multiple_programs
}
#[cfg(all(feature = "testing", feature = "long-benchmarks"))]
criterion_main!(long_benchmarks);
#[cfg(all(feature = "testing", not(any(feature = "long-benchmarks"))))]
criterion_main!(benchmarks);
