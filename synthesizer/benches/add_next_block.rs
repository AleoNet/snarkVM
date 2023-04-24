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

use console::program::{Identifier, ProgramID};

use criterion::Criterion;
use snarkvm_synthesizer::Program;

use std::str::FromStr;

// Note: The number of commands that can be included in a finalize block must be within the range [1, 255].
const NUM_COMMANDS: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128, 255];
const NUM_EXECUTIONS: &[usize] = &[2, 4, 8, 16, 32, 64, 128, 256];

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
        bench_add_next_block(
            c,
            format!("static_get/{num_commands}_commands"),
            &[Program::from_str(&program_string).unwrap()],
            &[(ProgramID::from_str("static_get.aleo").unwrap(), Identifier::from_str("initialize").unwrap(), vec![])],
            &[],
            &[(ProgramID::from_str("static_get.aleo").unwrap(), Identifier::from_str("getter").unwrap(), vec![])],
            &[1],
        );
    }

    bench_add_next_block(
        c,
        format!("static_get/{}_commands", NUM_COMMANDS.last().unwrap()),
        &[Program::from_str(&program_string).unwrap()],
        &[(ProgramID::from_str("static_get.aleo").unwrap(), Identifier::from_str("initialize").unwrap(), vec![])],
        &[],
        &[(ProgramID::from_str("static_get.aleo").unwrap(), Identifier::from_str("getter").unwrap(), vec![])],
        NUM_EXECUTIONS,
    )
}

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
        bench_add_next_block(
            c,
            format!("static_init/{num_commands}_commands"),
            &[Program::from_str(&program_string).unwrap()],
            &[],
            &[],
            &[(ProgramID::from_str("static_init.aleo").unwrap(), Identifier::from_str("init").unwrap(), vec![])],
            &[1],
        );
    }

    bench_add_next_block(
        c,
        format!("static_init/{}_commands", NUM_COMMANDS.last().unwrap()),
        &[Program::from_str(&program_string).unwrap()],
        &[],
        &[],
        &[(ProgramID::from_str("static_init.aleo").unwrap(), Identifier::from_str("init").unwrap(), vec![])],
        NUM_EXECUTIONS,
    )
}

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
            program_string.push_str("set 0field into balances[0field];");
        }
        commands_added = *num_commands;
        bench_add_next_block(
            c,
            format!("static_set/{num_commands}_commands"),
            &[Program::from_str(&program_string).unwrap()],
            &[],
            &[],
            &[(ProgramID::from_str("static_set.aleo").unwrap(), Identifier::from_str("setter").unwrap(), vec![])],
            &[1],
        );
    }

    bench_add_next_block(
        c,
        format!("static_set/{}_commands", NUM_COMMANDS.last().unwrap()),
        &[Program::from_str(&program_string).unwrap()],
        &[],
        &[],
        &[(ProgramID::from_str("static_set.aleo").unwrap(), Identifier::from_str("setter").unwrap(), vec![])],
        NUM_EXECUTIONS,
    );
}

criterion_group! {
    name = add_next_block;
    config = Criterion::default().sample_size(10);
    targets = bench_static_get, bench_static_get_or_init, bench_static_set,
}

criterion_main!(add_next_block);
