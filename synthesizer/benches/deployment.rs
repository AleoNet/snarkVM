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
use std::borrow::BorrowMut;

mod utilities;
use utilities::*;

use console::network::Testnet3;
use snarkvm_synthesizer::{ConsensusStorage, Program, Transaction, VM};

use criterion::{BatchSize, Criterion};
use std::fmt::Display;

// Note: The number of commands that can be included in a finalize block must be within the range [1, 255].
const NUM_COMMANDS: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128, 255];
const NUM_DEPLOYMENTS: &[usize] = &[2, 4, 8, 16, 32, 64, 128, 256];
// Note: The maximum number of mappings that can be included in a program is 31.
const NUM_MAPPINGS: &[usize] = &[1, 2, 4, 8, 16, 31];
const NUM_PROGRAMS: &[usize] = &[2, 4, 8, 16, 32, 64];

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
#[cfg(feature = "testing")]
#[allow(unused)]
pub fn bench_deployment<C: ConsensusStorage<Testnet3>>(
    c: &mut Criterion,
    header: impl Display,
    mut workload: Workload,
) {
    // Setup the workload.
    let (vm, private_key, benchmark_transactions, mut rng, temp_dir) = workload.setup::<C>();

    // Run the benchmarks
    for (name, transactions) in benchmark_transactions {
        assert!(!transactions.is_empty(), "There must be at least one operation to benchmark.");

        let mut num_transactions = 0f64;
        let mut num_rejected = 0f64;

        let txns = vm.speculate(transactions.iter()).unwrap();

        c.bench_function(&format!("{header}/{name}/finalize"), |b| {
            b.iter_batched(
                || {
                    vm.finalize_store().start_atomic();
                    clean_finalize_state(&vm, &transactions);
                    vm.finalize_store().finish_atomic();
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
        clean_finalize_state(&vm, &transactions);
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
