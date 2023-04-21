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

use std::{fmt::Display, str::FromStr};
use utilities::*;

use console::{
    account::PrivateKey,
    network::{Network, Testnet3},
    program::{Identifier, ProgramID, Value},
    types::Field,
};
use snarkvm_synthesizer::{Program, Speculate, Transaction, Transactions};
use snarkvm_utilities::{TestRng, ToBytes};

use criterion::{BatchSize, Criterion};

// Note: The number of commands that can be included in a finalize block must be within the range [1, 255].
const NUM_COMMANDS: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128, 255];
const NUM_EXECUTIONS: &[usize] = &[2, 4, 8, 16, 32, 64, 128, 256];

#[cfg(feature = "test-utilities")]
fn bench_execution(
    c: &mut Criterion,
    name: impl Display,
    initialize: &[(ProgramID<Testnet3>, Identifier<Testnet3>, Vec<Value<Testnet3>>)],
    program: &Program<Testnet3>,
    function_name: &Identifier<Testnet3>,
    inputs: &[Value<Testnet3>],
    runs: &[usize],
) {
    let rng = &mut TestRng::default();

    // Sample a new private key and address.
    let private_key = PrivateKey::<Testnet3>::new(rng).unwrap();

    // Initialize the VM.
    let (vm, record) = initialize_vm(&private_key, rng);

    // Deploy the program.
    let program_size = program.to_bytes_le().unwrap().len();
    let deployment_transaction =
        Transaction::deploy(&vm, &private_key, program, (record, program_size as u64), None, rng).unwrap();
    vm.finalize(&Transactions::from(&[deployment_transaction]), None).unwrap();

    // Run the initialization transactions.
    for (program_id, identifier, values) in initialize {
        let authorization = vm.authorize(&private_key, program_id, identifier, values, rng).unwrap();
        let (_, execution, _) = vm.execute(authorization, None, rng).unwrap();
        let transaction = Transaction::from_execution(execution, None).unwrap();
        vm.finalize(&Transactions::from(&[transaction]), None).unwrap();
    }

    // Construct the execution transaction.
    let authorization = vm.authorize(&private_key, program.id(), function_name, inputs, rng).unwrap();
    let (_, execution, _) = vm.execute(authorization, None, rng).unwrap();

    let mut transactions = vec![];

    for num_executions in runs {
        // Construct the required number of transactions.
        for i in transactions.len()..*num_executions {
            transactions.push(Transaction::from_execution_unchecked(
                <Testnet3 as Network>::TransactionID::from(Field::from_u64(i as u64)),
                execution.clone(),
                None,
            ));
        }

        // Construct a `Speculate` object.
        let mut speculate = Speculate::new(vm.program_store().current_storage_root());

        // Benchmark speculation.
        c.bench_function(&format!("{}/{}_executions/speculate", name, num_executions), |b| {
            b.iter_batched(
                || speculate.clone(),
                |mut speculate| {
                    let accepted_transactions = speculate.speculate_transactions(&vm, &transactions).unwrap();
                    assert_eq!(transactions.len(), accepted_transactions.len());
                },
                BatchSize::SmallInput,
            )
        });

        // Speculate the transaction.
        speculate.speculate_transactions(&vm, &transactions).unwrap();

        // Benchmark the commit operation.
        c.bench_function(&format!("{}/{}_executions/commit", name, num_executions), |b| {
            b.iter_batched(|| speculate.clone(), |speculate| speculate.commit(&vm).unwrap(), BatchSize::SmallInput)
        });
    }
}

#[cfg(feature = "test-utilities")]
fn bench_static_set(c: &mut Criterion) {
    let mut program_string = r"
program static_set.aleo;
mapping balances:
    key left as field.public;
    value right as field.public;
function setter:
    finalize;
finalize setter:"
        .to_string();

    let mut commands_added = 0;
    for num_commands in NUM_COMMANDS {
        // Construct the program.
        for _ in commands_added..*num_commands {
            program_string.push_str(&"set 0field into balances[0field];");
        }
        commands_added = *num_commands;
        bench_execution(
            c,
            format!("static_set/{}_commands", num_commands),
            &[],
            &Program::from_str(&program_string).unwrap(),
            &Identifier::from_str("setter").unwrap(),
            &[],
            &[1],
        );
    }

    bench_execution(
        c,
        format!("static_set/{}_commands", NUM_COMMANDS.last().unwrap()),
        &[],
        &Program::from_str(&program_string).unwrap(),
        &Identifier::from_str("setter").unwrap(),
        &[],
        NUM_EXECUTIONS,
    );
}

#[cfg(feature = "test-utilities")]
fn bench_static_get_or_init(c: &mut Criterion) {
    let mut program_string = r"
program static_init.aleo;
mapping balances:
    key left as field.public;
    value right as field.public;
function init:
    finalize;
finalize init:"
        .to_string();

    let mut commands_added = 0;
    for num_commands in NUM_COMMANDS {
        // Construct the program.
        for i in commands_added..*num_commands {
            program_string.push_str(&format!("get.or_init balances[0field] 0field into r{i};"));
        }
        commands_added = *num_commands;
        bench_execution(
            c,
            format!("static_init/{}_commands", num_commands),
            &[],
            &Program::from_str(&program_string).unwrap(),
            &Identifier::from_str("init").unwrap(),
            &[],
            &[1],
        );
    }

    bench_execution(
        c,
        format!("static_init/{}_commands", NUM_COMMANDS.last().unwrap()),
        &[],
        &Program::from_str(&program_string).unwrap(),
        &Identifier::from_str("init").unwrap(),
        &[],
        NUM_EXECUTIONS,
    );
}

#[cfg(feature = "test-utilities")]
fn bench_static_get(c: &mut Criterion) {
    let mut program_string = r"
program static_get.aleo;
mapping balances:
    key left as field.public;
    value right as field.public;
function initialize:
    finalize;
finalize initialize:
    set 0field into balances[0field];
function getter:
    finalize;
finalize getter:"
        .to_string();

    let mut commands_added = 0;
    for num_commands in NUM_COMMANDS {
        // Construct the program.
        for i in commands_added..*num_commands {
            program_string.push_str(&format!("get balances[0field] into r{i};"));
        }
        commands_added = *num_commands;
        bench_execution(
            c,
            format!("static_get/{}_commands", num_commands),
            &[(ProgramID::from_str("static_get.aleo").unwrap(), Identifier::from_str("initialize").unwrap(), vec![])],
            &Program::from_str(&program_string).unwrap(),
            &Identifier::from_str("getter").unwrap(),
            &[],
            &[1],
        );
    }

    bench_execution(
        c,
        format!("static_get/{}_commands", NUM_COMMANDS.last().unwrap()),
        &[(ProgramID::from_str("static_get.aleo").unwrap(), Identifier::from_str("initialize").unwrap(), vec![])],
        &Program::from_str(&program_string).unwrap(),
        &Identifier::from_str("getter").unwrap(),
        &[],
        NUM_EXECUTIONS,
    );
}

criterion_group! {
    name = execution;
    config = Criterion::default().sample_size(10);
    // targets = bench_static_set, bench_static_get_or_init, bench_static_get,
    targets = bench_static_get
}

criterion_main!(execution);
