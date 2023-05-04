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

use console::{account::PrivateKey, network::Testnet3};
use snarkvm_synthesizer::{helpers::memory::ConsensusMemory, ConsensusStorage, Speculate, Transaction};
use snarkvm_utilities::TestRng;

use criterion::{BatchSize, Criterion};
use std::fmt::Display;

// Note: The number of commands that can be included in a finalize block must be within the range [1, 255].
const NUM_COMMANDS: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128, 255];
const NUM_EXECUTIONS: &[usize] = &[2, 4, 8, 16, 32, 64];
const NUM_PROGRAMS: &[usize] = &[2, 4, 8, 16, 32, 64];

/// A helper function for benchmarking `Speculate::speculate`.
#[cfg(feature = "testing")]
#[allow(unused)]
pub fn bench_speculate<C: ConsensusStorage<Testnet3>>(
    c: &mut Criterion,
    header: impl Display,
    mut workload: Workload,
) {
    // Setup the workload.
    let (vm, private_key, benchmark_transactions, rng) = workload.setup::<C>();

    // Benchmark each of the programs.
    for (name, transactions) in benchmark_transactions {
        assert!(!transactions.is_empty(), "There must be at least one transaction to benchmark.");

        // Construct a `Speculate` object.
        let mut speculate = Speculate::new(vm.finalize_store().current_finalize_root());

        // Benchmark speculation.
        c.bench_function(&format!("{header}/{name}/speculate"), |b| {
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
    // Initialize the workload.
    let mut workload = Workload::new("speculate_one_operation".to_string(), vec![]).unwrap();
    for num_commands in NUM_COMMANDS {
        workload.add(Box::new(StaticGet::new(1, *num_commands, 1, 1)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(StaticGetOrInit::new(1, *num_commands, 1, 1)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(StaticSet::new(1, *num_commands, 1, 1)) as Box<dyn Benchmark<Testnet3>>);
    }
    workload.add(Box::new(MintPublic::new(1)) as Box<dyn Benchmark<Testnet3>>);
    workload.add(Box::new(TransferPrivateToPublic::new(1)) as Box<dyn Benchmark<Testnet3>>);
    workload.add(Box::new(TransferPublic::new(1)) as Box<dyn Benchmark<Testnet3>>);
    workload.add(Box::new(TransferPublicToPrivate::new(1)) as Box<dyn Benchmark<Testnet3>>);

    #[cfg(not(any(feature = "rocks")))]
    bench_speculate::<ConsensusMemory<Testnet3>>(c, "memory", workload);
    #[cfg(any(feature = "rocks"))]
    bench_speculate::<snarkvm_synthesizer::helpers::rocksdb::ConsensusDB<Testnet3>>(c, "db", workload);
}

fn bench_multiple_operations(c: &mut Criterion) {
    // Initialize the workloads.
    let mut workload = Workload::new("speculate_multiple_operations".to_string(), vec![]).unwrap();
    let max_commands = *NUM_COMMANDS.last().unwrap();
    for num_executions in NUM_EXECUTIONS {
        workload.add(Box::new(StaticGet::new(1, max_commands, *num_executions, 1)) as Box<dyn Benchmark<Testnet3>>);
        workload
            .add(Box::new(StaticGetOrInit::new(1, max_commands, *num_executions, 1)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(StaticSet::new(1, max_commands, *num_executions, 1)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(MintPublic::new(*num_executions)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(TransferPrivateToPublic::new(*num_executions)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(TransferPublic::new(*num_executions)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(TransferPublicToPrivate::new(*num_executions)) as Box<dyn Benchmark<Testnet3>>);
    }

    #[cfg(not(any(feature = "rocks")))]
    bench_speculate::<ConsensusMemory<Testnet3>>(c, "memory", workload);
    #[cfg(any(feature = "rocks"))]
    bench_speculate::<snarkvm_synthesizer::helpers::rocksdb::ConsensusDB<Testnet3>>(c, "db", workload);
}

fn bench_multiple_operations_with_multiple_programs(c: &mut Criterion) {
    // Initialize the workloads.
    let max_commands = *NUM_COMMANDS.last().unwrap();
    let max_executions = *NUM_EXECUTIONS.last().unwrap();
    let mut workload = Workload::new("speculate_multiple_operations_with_multiple_programs".to_string(), vec![]).unwrap();
    for num_programs in NUM_PROGRAMS {
        workload
            .add(Box::new(StaticGet::new(1, max_commands, max_executions, *num_programs))
                as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(StaticGetOrInit::new(1, max_commands, max_executions, *num_programs))
            as Box<dyn Benchmark<Testnet3>>);
        workload
            .add(Box::new(StaticSet::new(1, max_commands, max_executions, *num_programs))
                as Box<dyn Benchmark<Testnet3>>);
    }

    #[cfg(not(any(feature = "rocks")))]
    bench_speculate::<ConsensusMemory<Testnet3>>(c, "memory", workload);
    #[cfg(any(feature = "rocks"))]
    bench_speculate::<snarkvm_synthesizer::helpers::rocksdb::ConsensusDB<Testnet3>>(c, "db", workload);
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
#[cfg(all(feature = "testing", feature = "long-benchmarks"))]
criterion_main!(long_benchmarks);
#[cfg(all(feature = "testing", not(any(feature = "long-benchmarks"))))]
criterion_main!(benchmarks);
