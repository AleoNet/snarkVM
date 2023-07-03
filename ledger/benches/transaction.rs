// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![allow(clippy::type_complexity)]

#[macro_use]
extern crate criterion;

use console::{
    account::*,
    network::Testnet3,
    program::{Plaintext, Record, Value},
};
use ledger_block::Transition;
use ledger_store::{helpers::memory::ConsensusMemory, ConsensusStore};
use synthesizer::{process::Authorization, program::Program, VM};

use criterion::Criterion;
use indexmap::IndexMap;

fn initialize_vm<R: Rng + CryptoRng>(
    private_key: &PrivateKey<Testnet3>,
    rng: &mut R,
) -> (VM<Testnet3, ConsensusMemory<Testnet3>>, Vec<Record<Testnet3, Plaintext<Testnet3>>>) {
    let vm = VM::from(ConsensusStore::open(None).unwrap()).unwrap();

    // Initialize the genesis block.
    let genesis = vm.genesis(private_key, rng).unwrap();

    // Fetch the unspent records.
    let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();

    // Select a record to spend.
    let view_key = ViewKey::try_from(private_key).unwrap();
    let records = records.values().map(|record| record.decrypt(&view_key).unwrap()).collect();

    // Update the VM.
    vm.add_next_block(&genesis).unwrap();

    (vm, records)
}

fn deploy(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    // Sample a new private key and address.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();

    // Initialize the VM.
    let (vm, records) = initialize_vm(&private_key, rng);

    // Create a sample program.
    let program = Program::<Testnet3>::from_str(
        r"
program helloworld.aleo;

function hello:
    input r0 as u32.private;
    input r1 as u32.private;
    add r0 r1 into r2;
    output r2 as u32.private;
",
    )
    .unwrap();

    c.bench_function("Transaction - deploy", |b| {
        b.iter(|| vm.deploy(&private_key, &program, (records[0].clone(), 600000), None, rng).unwrap())
    });

    c.bench_function("Transaction verify - deployment", |b| {
        let transaction = vm.deploy(&private_key, &program, (records[0].clone(), 600000), None, rng).unwrap();
        b.iter(|| assert!(vm.verify_transaction(&transaction, None)))
    });
}

fn execute(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    // Sample a new private key and address.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();
    let address = Address::try_from(&private_key).unwrap();

    // Initialize the VM.
    let (vm, records) = initialize_vm(&private_key, rng);

    // Prepare the inputs.
    let inputs = [
        Value::<Testnet3>::Record(records[0].clone()),
        Value::<Testnet3>::from_str(&address.to_string()).unwrap(),
        Value::<Testnet3>::from_str("1u64").unwrap(),
    ]
    .into_iter();

    // Authorize.
    let authorization = vm.authorize(&private_key, "credits.aleo", "transfer_private", inputs, rng).unwrap();

    let (_, fee) = vm.execute_fee_raw(&private_key, records[1].clone(), 100000, Field::zero(), None, rng).unwrap();

    c.bench_function("Transaction - execution (transfer)", |b| {
        b.iter(|| {
            vm.execute_authorization(
                Authorization::new(&authorization.to_vec_deque().into_iter().collect::<Vec<_>>()),
                Some(fee.clone()),
                None,
                rng,
            )
            .unwrap();
        })
    });

    c.bench_function("Transaction verify - execution (transfer)", |b| {
        let transaction = vm
            .execute_authorization(
                Authorization::new(&authorization.to_vec_deque().into_iter().collect::<Vec<_>>()),
                Some(fee.clone()),
                None,
                rng,
            )
            .unwrap();
        b.iter(|| assert!(vm.verify_transaction(&transaction, None)))
    });
}

criterion_group! {
    name = transaction;
    config = Criterion::default().sample_size(10);
    targets = deploy, execute
}

criterion_main!(transaction);
