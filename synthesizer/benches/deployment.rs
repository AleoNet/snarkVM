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

// Note: 32 is the maximum number of mappings that can be included in a single program.
const NUM_MAPPINGS: &[usize] = &[0, 1, 2, 4, 8, 16, 32];
const NUM_PROGRAMS: &[usize] = &[10, 100, 1000, 10000];

#[cfg(feature = "test-utilities")]
fn single_deployment(c: &mut Criterion) {
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

    for num_mappings in NUM_MAPPINGS {
        // Construct a new program.
        let program =
            construct_program(ProgramConfig { num_mappings: *num_mappings, transition_configs: vec![] }, &mut namer);

        // Construct a deployment transaction.
        let deployment = Deployment::new_unchecked(<Testnet3 as Network>::EDITION, program, vec![]);
        let transaction = Transaction::from_deployment_unchecked(id, owner, deployment, fee.clone());

        // Construct a `Speculate` object.
        let mut speculate = Speculate::new(vm.program_store().current_storage_root());

        // Benchmark the speculation with the given number of mappings.
        c.bench_function(&format!("speculate_single_deployment/{}_mappings", num_mappings), |b| {
            b.iter_batched(
                || speculate.clone(),
                |mut speculate| speculate.speculate_transaction(&vm, &transaction).unwrap(),
                BatchSize::SmallInput,
            )
        });

        // Speculate the transaction.
        speculate.speculate_transaction(&vm, &transaction).unwrap();

        // Benchmark the commit operation with the given number of mappings.
        c.bench_function(&format!("commit_single_deployment/{}_mappings", num_mappings), |b| {
            b.iter_batched(|| speculate.clone(), |speculate| speculate.commit(&vm).unwrap(), BatchSize::SmallInput)
        });
    }
}

#[cfg(feature = "test-utilities")]
fn multiple_deployments(c: &mut Criterion) {
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

    for num_programs in NUM_PROGRAMS {
        // Add the required number of transactions
        for i in transactions.len()..*num_programs {
            let id = <Testnet3 as Network>::TransactionID::from(Field::from_u64(i as u64));
            let owner = Owner::new(&private_key, id, rng).unwrap();
            transactions.push(Transaction::from_deployment_unchecked(id, owner, deployment.clone(), fee.clone()));
        }

        // Construct a `Speculate` object.
        let mut speculate = Speculate::new(vm.program_store().current_storage_root());

        // Benchmark speculation with the given number of programs.
        c.bench_function(&format!("speculate_multiple_deployments/{}_programs", num_programs), |b| {
            b.iter_batched(
                || speculate.clone(),
                |mut speculate| speculate.speculate_transactions(&vm, &transactions).unwrap(),
                BatchSize::SmallInput,
            )
        });

        // Speculate the transactions.
        speculate.speculate_transactions(&vm, &transactions).unwrap();

        // Benchmark the commit operation with the given number of programs.
        c.bench_function(&format!("commit_multiple_deployments/{}_programs", num_programs), |b| {
            b.iter_batched(|| speculate.clone(), |speculate| speculate.commit(&vm).unwrap(), BatchSize::SmallInput)
        });
    }
}

criterion_group! {
    name = deployment;
    config = Criterion::default().sample_size(10);
    targets = single_deployment, multiple_deployments
}

criterion_main!(deployment);
