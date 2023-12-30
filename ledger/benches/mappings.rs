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
    network::{
        prelude::{TestRng, Uniform},
        Testnet3,
    },
    prelude::{FromBytes, Itertools, Network},
    program::{Identifier, Literal, Plaintext, ProgramID, Register, Value},
    types::U64,
};
use ledger_block::Block;
use ledger_store::ConsensusStore;
use synthesizer::{
    prelude::FinalizeRegisters,
    process::FinalizeTypes,
    program::{FinalizeGlobalState, FinalizeStoreTrait, RegistersStore},
    Command,
    Finalize,
    Program,
    Stack,
    VM,
};

use criterion::{BatchSize, Criterion};

use std::{str::FromStr, time::Duration};

type CurrentNetwork = Testnet3;
#[cfg(not(feature = "rocks"))]
type ConsensusType<N> = ledger_store::helpers::memory::ConsensusMemory<N>;
#[cfg(not(feature = "rocks"))]
const STORE_TYPE: &str = "memory";
#[cfg(feature = "rocks")]
type ConsensusType<N> = ledger_store::helpers::rocksdb::ConsensusDB<N>;
#[cfg(feature = "rocks")]
const STORE_TYPE: &str = "rocksdb";

// Initialize the commands we want to benchmark
const COMMANDS: [&str; 4] = ["contains", "get", "get.or_use", "set"];
// Initialize the types of mappings we want to benchmark
const MAPPING_TYPES: [&str; 14] = [
    "field",
    "group",
    "u64",
    "[field; 2u32]",
    "[field; 4u32]",
    "[field; 8u32]",
    "[field; 16u32]",
    "[[field; 2u32]; 2u32]",
    "[[field; 4u32]; 4u32]",
    "[[field; 8u32]; 8u32]",
    "[[field; 16u32]; 16u32]",
    "[[[field; 2u32]; 2u32]; 2u32]",
    "[[[field; 4u32]; 4u32]; 4u32]",
    "[[[field; 8u32]; 8u32]; 8u32]",
];
// Initialize names for the mappings
const MAPPING_NAMES: [&str; 14] = [
    "m_field",
    "m_group",
    "m_u64",
    "m_field_array_depth_0_length_2",
    "m_field_array_depth_0_length_4",
    "m_field_array_depth_0_length_8",
    "m_field_array_depth_0_length_16",
    "m_field_array_depth_1_length_2",
    "m_field_array_depth_1_length_4_",
    "m_field_array_depth_1_length_8",
    "m_field_array_depth_1_length_16",
    "m_field_array_depth_2_length_2",
    "m_field_array_depth_2_length_4",
    "m_field_array_depth_2_length_8",
];
// Initialize the number of entries we want to benchmark each command on
const NUM_ENTRIES: [u64; 8] = [1, 1000, 10_000, 50_000, 100_000, 200_000, 500_000, 1_000_000];

// Generate an input for the given mapping name
fn generate_input(mapping_name: &str, rng: &mut TestRng) -> Value<CurrentNetwork> {
    if mapping_name == "m_u64" {
        let arg: U64<CurrentNetwork> = Uniform::rand(rng);
        Value::from_str(&arg.to_string()).unwrap()
    } else if mapping_name == "m_field" {
        let arg: console::types::Field<CurrentNetwork> = Uniform::rand(rng);
        Value::from_str(&arg.to_string()).unwrap()
    } else if mapping_name == "m_group" {
        let arg: console::types::Group<CurrentNetwork> = Uniform::rand(rng);
        Value::from_str(&arg.to_string()).unwrap()
    } else if mapping_name.contains("array") {
        let arg: console::types::Field<CurrentNetwork> = Uniform::rand(rng);
        let parts: Vec<&str> = mapping_name.split('_').collect();
        let depth = parts[4].trim_start_matches("depth").parse::<usize>().unwrap() + 1;
        let length = parts[6].trim_start_matches("length").parse::<usize>().unwrap();

        // Build the input
        let mut input = String::new();
        if depth > 0 {
            // Create the basic element
            let mut inner_array = format!("{}, ", arg).repeat(length);
            inner_array.truncate(inner_array.len() - 2);

            // Create the nested input
            for _ in 1..depth {
                inner_array = format!("[{}], ", inner_array).repeat(length);
                inner_array.truncate(inner_array.len() - 2);
            }

            // Enclose it in an outer array
            input.push_str(&format!("[{}]", inner_array));
        } else {
            input.push_str(&format!("{}", arg));
        };
        Value::from_str(&input).unwrap()
    } else {
        panic!("Invalid mapping type")
    }
}

// Setup the registers needed to execute the given command
fn setup_registers(
    rng: &mut TestRng,
    input_type: &str,
    mapping_name: &str,
    command: &str,
    index: u64,
    stack: &Stack<CurrentNetwork>,
) -> FinalizeRegisters<CurrentNetwork> {
    // Construct the finalize string.
    let mut finalize_string = "finalize foo:".to_string();
    finalize_string.push_str("input r0 as u64.public;");
    if command.contains("set") || command.contains("get.or_use") {
        finalize_string.push_str(&format!("input r1 as {input_type}.public;"));
    };
    finalize_string.push_str(command);

    // Construct the FinalizeState & Finalize.
    let state =
        FinalizeGlobalState::new::<CurrentNetwork>(0, 0, 0, 0, <Testnet3 as Network>::BlockHash::default()).unwrap();
    let finalize = Finalize::<CurrentNetwork>::from_str(&finalize_string).unwrap();

    // Initialize a fresh set of finalize registers.
    let mut registers = FinalizeRegisters::new(
        state,
        <Testnet3 as Network>::TransitionID::default(),
        Identifier::from_str("test").unwrap(),
        FinalizeTypes::from_finalize(stack, &finalize).unwrap(),
    );

    // Add the arguments into the registers.
    registers.store(stack, &Register::Locator(0u64), Value::from(Literal::U64(U64::new(index)))).unwrap();
    if command.contains("set") || command.contains("get.or_use") {
        registers.store(stack, &Register::Locator(1u64), generate_input(mapping_name, rng)).unwrap();
    }
    registers
}

fn bench_mappings(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    // Initialize storage.
    println!("Initializing storage...");
    let storage = ConsensusStore::<CurrentNetwork, ConsensusType<CurrentNetwork>>::open(Some(0)).unwrap();

    // Initialize the VM.
    println!("Initializing the VM...");
    let vm = VM::<CurrentNetwork, _>::from(storage).unwrap();
    let genesis_block = &Block::read_le(Testnet3::genesis_bytes()).unwrap();
    vm.add_next_block(genesis_block).unwrap();

    let program = Program::<CurrentNetwork>::from_str(include_str!("mappings.aleo")).unwrap();
    vm.process().write().add_program(&program).unwrap();

    // Construct the program ID to index the mapping with and construct the finalize store
    println!("Initializing the Finalize store...");
    let program_id = ProgramID::from_str("mappings.aleo").unwrap();
    let finalize_store = vm.finalize_store();

    // Initialize a mapping for each type
    MAPPING_NAMES.into_iter().for_each(|mapping_name| {
        println!("Initializing mapping {mapping_name}...");
        let mapping_name = Identifier::<CurrentNetwork>::from_str(mapping_name).unwrap();
        finalize_store.initialize_mapping(program_id, mapping_name).unwrap();
    });
    let stack = (*vm.process().read().get_stack("mappings.aleo").unwrap().clone()).clone();

    // Bench each mapping type over contains, get, get.or_use, and store.
    let mut previous_entries = 0;
    for (mapping_type, mapping_name) in MAPPING_TYPES.into_iter().zip_eq(MAPPING_NAMES) {
        for num_entries in NUM_ENTRIES {
            // Pre-Populate the store with the desired number of entries.
            (previous_entries..num_entries).for_each(|i| {
                // Increment the key and generate a random value to insert.
                let key = Plaintext::<CurrentNetwork>::from(Literal::U64(U64::new(i)));
                let value = generate_input(mapping_name, rng);
                let identifier = Identifier::<CurrentNetwork>::from_str(mapping_name).unwrap();
                finalize_store.insert_key_value(program_id, identifier, key, value).unwrap();
            });
            previous_entries = num_entries + 1;

            for command in COMMANDS {
                let benchmark_name = format!(
                    "{command}_{}_{num_entries}_entries_{STORE_TYPE}",
                    mapping_name.strip_prefix("m_").unwrap()
                );
                // Construct the command
                println!("Benching {benchmark_name}");

                // Create the bench command
                let command_string = if command == "set" {
                    format!("set r1 into {mapping_name}[r0];")
                } else if command == "get.or_use" {
                    format!("get.or_use {mapping_name}[r0] r1 into r2;")
                } else {
                    format!("{command} {mapping_name}[r0] into r1;")
                };

                // Measure the time it takes to execute the command.
                c.bench_function(&benchmark_name, |b| {
                    b.iter_batched(
                        || {
                            let command = Command::<CurrentNetwork>::from_str(&command_string).unwrap();
                            let registers =
                                setup_registers(rng, mapping_type, mapping_name, &command_string, num_entries, &stack);
                            (command, registers)
                        },
                        |(command, mut registers)| command.finalize(&stack, finalize_store, &mut registers),
                        BatchSize::PerIteration,
                    )
                });
            }
        }
    }
}

criterion_group! {
    name = mappings;
    config = Criterion::default().sample_size(10).measurement_time(Duration::from_secs(10));
    targets = bench_mappings
}
criterion_main!(mappings);
