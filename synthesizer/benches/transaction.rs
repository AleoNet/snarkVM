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

use console::{
    account::*,
    network::Testnet3,
    program::{Plaintext, Record, Value},
};
use snarkvm_synthesizer::{
    store::helpers::memory::ConsensusMemory,
    Authorization,
    Block,
    ConsensusStore,
    Program,
    Transaction,
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
    let genesis = Block::genesis(&vm, private_key, rng).unwrap();

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
        b.iter(|| Transaction::deploy(&vm, &private_key, &program, (record.clone(), 600000), None, rng).unwrap())
    });

    c.bench_function("Transaction verify - deployment", |b| {
        let transaction =
            Transaction::deploy(&vm, &private_key, &program, (record.clone(), 600000), None, rng).unwrap();
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
            Transaction::execute_authorization(
                &vm,
                Authorization::new(&authorization.to_vec_deque().into_iter().collect::<Vec<_>>()),
                None,
                None,
                rng,
            )
            .unwrap();
        })
    });

    c.bench_function("Transaction verify - execution (transfer)", |b| {
        let transaction = Transaction::execute_authorization(
            &vm,
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
