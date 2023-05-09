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
use snarkvm_synthesizer::{ConsensusStorage, Transaction, VM};

use criterion::{BatchSize, Criterion};
use std::fmt::Display;

const NUM_DEPLOYMENTS: &[usize] = &[2, 4, 8, 16, 32, 64, 128, 256];
// Note: The maximum number of mappings that can be included in a program is 31.
const NUM_MAPPINGS: &[usize] = &[1, 2, 4, 8, 16, 31];

/// A helper function to remove programs, from a set of deployment transactions, from the finalize store.
fn clean_finalize_state<C: ConsensusStorage<Testnet3>>(vm: &VM<Testnet3, C>, transactions: &[Transaction<Testnet3>]) {
    for transaction in transactions {
        match transaction {
            Transaction::Deploy(_, _, deployment, _) => {
                let program = deployment.program();
                if vm.finalize_store().contains_program_confirmed(program.id()).unwrap() {
                    for (mapping_name, _) in program.mappings() {
                        vm.finalize_store().remove_mapping(program.id(), mapping_name).unwrap();
                        vm.process().write().remove_program(program.id()).unwrap();
                    }
                    vm.finalize_store().remove_program(program.id()).unwrap();
                }
            }
            _ => unreachable!("The benchmark should only contain deployment transactions."),
        }
    }
}

/// A helper function for benchmarking deployments.
pub fn bench_deployment<C: ConsensusStorage<Testnet3>>(
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

        // Benchmark `speculate`.
        c.bench_function(&format!("{header}/{name}/speculate"), |b| {
            b.iter_batched(|| {}, |_| vm.speculate(transactions.iter()).unwrap(), BatchSize::SmallInput)
        });

        // Construct the `Transactions` object.
        let txns = vm.speculate(transactions.iter()).unwrap();

        // Benchmark `finalize`.
        c.bench_function(&format!("{header}/{name}/finalize"), |b| {
            b.iter_batched(
                || {
                    vm.finalize_store().start_atomic();
                    clean_finalize_state(&vm, &transactions);
                    vm.finalize_store().finish_atomic().unwrap();
                    num_transactions += txns.iter().count() as f64;
                    num_rejected += txns.iter().filter(|t| t.is_rejected()).count() as f64;
                },
                |_| {
                    vm.finalize(&txns).unwrap();
                },
                BatchSize::PerIteration,
            )
        });

        // Clean up the VM.
        vm.finalize_store().start_atomic();
        clean_finalize_state(&vm, &transactions);
        vm.finalize_store().finish_atomic().unwrap();

        // Construct the next block.
        let block = construct_next_block(&vm, &private_key, &transactions, &mut rng).unwrap();
        // Add the block to the VM.
        // This is done to ensure that there is a block that can be safely removed from the block store at the beginning of each iteration.
        vm.add_next_block(&block).unwrap();

        // Benchmark `add_next_block`.
        c.bench_function(&format!("{header}/{name}/add_next_block"), |b| {
            b.iter_batched(
                || {
                    vm.finalize_store().start_atomic();
                    clean_finalize_state(&vm, &transactions);
                    vm.finalize_store().finish_atomic().unwrap();
                    vm.block_store().start_atomic();
                    vm.block_store().remove_last_n(1).unwrap();
                    vm.block_store().finish_atomic().unwrap();
                    num_transactions += block.transactions().iter().count() as f64;
                    num_rejected += block.transactions().iter().filter(|t| t.is_rejected()).count() as f64;
                },
                |_| {
                    vm.add_next_block(&block).unwrap();
                },
                BatchSize::PerIteration,
            )
        });

        // Clean up the VM.
        vm.finalize_store().start_atomic();
        clean_finalize_state(&vm, &transactions);
        vm.finalize_store().finish_atomic().unwrap();
        vm.block_store().start_atomic();
        vm.block_store().remove_last_n(1).unwrap();
        vm.block_store().finish_atomic().unwrap();

        println!(
            "| {header}/{name}/finalize | Transactions: {} | Rejected: {} | Percent Rejected: {}",
            num_transactions,
            num_rejected,
            (num_rejected / num_transactions) * 100.0
        );
    }
}

fn bench_single_deployment(c: &mut Criterion) {
    // Initialize the workload.
    let workload = single_deployment_workload(NUM_MAPPINGS);

    #[cfg(not(any(feature = "rocks")))]
    bench_finalize::<ConsensusMemory<Testnet3>>(c, "memory", workload);
    #[cfg(any(feature = "rocks"))]
    bench_deployment::<snarkvm_synthesizer::helpers::rocksdb::ConsensusDB<Testnet3>>(c, "db", workload);
}

fn bench_multiple_deployments(c: &mut Criterion) {
    // Initialize the workload.
    let workload = multiple_deployments_workload(NUM_DEPLOYMENTS, *NUM_MAPPINGS.last().unwrap());

    #[cfg(not(any(feature = "rocks")))]
    bench_finalize::<ConsensusMemory<Testnet3>>(c, "memory", workload);
    #[cfg(any(feature = "rocks"))]
    bench_deployment::<snarkvm_synthesizer::helpers::rocksdb::ConsensusDB<Testnet3>>(c, "db", workload);
}

criterion_group! {
    name = benchmarks;
    config = Criterion::default().sample_size(10);
    targets = bench_single_deployment, bench_multiple_deployments,
}
criterion_main!(benchmarks);
