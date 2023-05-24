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

#[macro_use]
extern crate criterion;

use console::{
    account::*,
    network::Testnet3,
    program::{Plaintext, Record, Value},
};
use snarkvm_synthesizer::{
    store::helpers::memory::ConsensusMemory,
    Authorization,
    ConsensusStore,
    Program,
    Transition,
    VM,
};

use criterion::Criterion;
use indexmap::IndexMap;
use rand::{CryptoRng, Rng};

fn initialize_vm<R: Rng + CryptoRng>(
    private_key: &PrivateKey<Testnet3>,
    rng: &mut R,
) -> (VM<Testnet3, ConsensusMemory<Testnet3>>, Record<Testnet3, Plaintext<Testnet3>>) {
    let vm = VM::from(ConsensusStore::open(None).unwrap()).unwrap();

    // Initialize the genesis block.
    let genesis = vm.genesis(private_key, rng).unwrap();

    // Fetch the unspent records.
    let records = genesis.transitions().cloned().flat_map(Transition::into_records).collect::<IndexMap<_, _>>();

    // Select a record to spend.
    let view_key = ViewKey::try_from(private_key).unwrap();
    let record = records.values().next().unwrap().decrypt(&view_key).unwrap();

    // Update the VM.
    vm.add_next_block(&genesis).unwrap();

    (vm, record)
}

fn deploy(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    // Sample a new private key and address.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();

    // Initialize the VM.
    let (vm, record) = initialize_vm(&private_key, rng);

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
        b.iter(|| vm.deploy(&private_key, &program, (record.clone(), 600000), None, rng).unwrap())
    });

    c.bench_function("Transaction verify - deployment", |b| {
        let transaction = vm.deploy(&private_key, &program, (record.clone(), 600000), None, rng).unwrap();
        b.iter(|| assert!(vm.verify_transaction(&transaction)))
    });
}

fn execute(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    // Sample a new private key and address.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();
    let address = Address::try_from(&private_key).unwrap();

    // Initialize the VM.
    let (vm, record) = initialize_vm(&private_key, rng);

    // Prepare the inputs.
    let inputs = [
        Value::<Testnet3>::Record(record),
        Value::<Testnet3>::from_str(&address.to_string()).unwrap(),
        Value::<Testnet3>::from_str("1u64").unwrap(),
    ]
    .into_iter();

    // Authorize.
    let authorization = vm.authorize(&private_key, "credits.aleo", "transfer", inputs, rng).unwrap();

    c.bench_function("Transaction - execution (transfer)", |b| {
        b.iter(|| {
            vm.execute_authorization(
                Authorization::new(&authorization.to_vec_deque().into_iter().collect::<Vec<_>>()),
                None,
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
                None,
                None,
                rng,
            )
            .unwrap();
        b.iter(|| assert!(vm.verify_transaction(&transaction)))
    });
}

criterion_group! {
    name = transaction;
    config = Criterion::default().sample_size(10);
    targets = deploy, execute
}

criterion_main!(transaction);
