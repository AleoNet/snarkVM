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

#[macro_use]
extern crate criterion;

mod utilities;
use utilities::*;

use console::{
    account::PrivateKey,
    network::{Network, Testnet3},
    types::Field,
};
use snarkvm_synthesizer::{Deployment, Owner, Speculate, Transaction};
use snarkvm_utilities::TestRng;

use criterion::{BatchSize, Criterion};

const NUM_MAPPINGS: &[usize] = &[0, 1, 2, 4, 8, 16, 32];
const NUM_PROGRAMS: &[usize] = &[10, 100, 1000, 10000, 100000];

#[cfg(feature = "test-utilities")]
fn commit_single_deployment(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    // Sample a new private key and address.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();

    // Initialize a `Namer` to help construct unique programs.
    let mut namer = Namer::new();

    // Initialize the VM.
    let (vm, record) = initialize_vm(&private_key, rng);

    // Compute placeholder data for the transaction.
    let id = <Testnet3 as Network>::TransactionID::default();
    let owner = Owner::new(&private_key, id, rng).unwrap();
    let (_, fee, _) = vm.execute_fee(&private_key, record, 1, None, rng).unwrap();

    // Create a new benchmark group.
    let mut group = c.benchmark_group("commit_single_deployment");
    for num_mappings in NUM_MAPPINGS {
        // Construct a new program.
        let program =
            construct_program(ProgramConfig { num_mappings: *num_mappings, transition_configs: vec![] }, &mut namer);

        // Construct a deployment transaction.
        let deployment = Deployment::new_unchecked(<Testnet3 as Network>::EDITION, program, vec![]);
        let transaction = Transaction::from_deployment_unchecked(id, owner, deployment, fee.clone());

        // Construct a `Speculate` object.
        let mut speculate = Speculate::new(vm.program_store().current_storage_root());

        // Speculate the transaction.
        speculate.speculate_transaction(&vm, &transaction).unwrap();

        // Benchmark the commit operation with the given number of mappings.
        group.bench_function(&format!("{}_mappings", num_mappings), |b| {
            b.iter_batched(|| speculate.clone(), |speculate| speculate.commit(&vm).unwrap(), BatchSize::SmallInput)
        });
    }
    group.finish();
}

#[cfg(feature = "test-utilities")]
fn commit_multiple_deployments(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    // Sample a new private key and address.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();

    // Initialize a `Namer` to help construct unique programs.
    let mut namer = Namer::new();

    // Initialize the VM.
    let (vm, record) = initialize_vm(&private_key, rng);

    // Construct a new program.
    let program = construct_program(
        ProgramConfig { num_mappings: *NUM_MAPPINGS.last().unwrap(), transition_configs: vec![] },
        &mut namer,
    );

    // Construct a fee and deployment for the transaction.
    let (_, fee, _) = vm.execute_fee(&private_key, record, 1, None, rng).unwrap();
    let deployment = Deployment::new_unchecked(<Testnet3 as Network>::EDITION, program, vec![]);

    // Construct a vector for transactions.
    let mut transactions = vec![];

    // Create a new benchmark group.
    let mut group = c.benchmark_group("commit_multiple_deployments");
    for num_programs in NUM_PROGRAMS {
        // Add the required number of transactions
        for i in transactions.len()..*num_programs {
            let id = <Testnet3 as Network>::TransactionID::from(Field::from_u64(i as u64));
            let owner = Owner::new(&private_key, id, rng).unwrap();
            transactions.push(Transaction::from_deployment_unchecked(id, owner, deployment.clone(), fee.clone()));
        }

        // Construct a `Speculate` object.
        let mut speculate = Speculate::new(vm.program_store().current_storage_root());

        // Speculate the transactions.
        speculate.speculate_transactions(&vm, &transactions).unwrap();

        // Benchmark the commit operation with the given number of programs.
        group.bench_function(&format!("{}_programs", num_programs), |b| {
            b.iter_batched(|| speculate.clone(), |speculate| speculate.commit(&vm).unwrap(), BatchSize::SmallInput)
        });
    }
    group.finish();
}

criterion_group! {
    name = commit_deployment;
    config = Criterion::default().sample_size(10);
    targets = commit_single_deployment, commit_multiple_deployments,
}

criterion_main!(commit_deployment);
