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

use crate::utilities::Namer;
use std::str::FromStr;

use console::{network::Testnet3, program::Identifier};
use snarkvm_synthesizer::{Function, Program};

pub struct ProgramConfig {
    pub num_mappings: usize,
    pub transition_configs: Vec<TransitionConfig>,
}

impl Default for ProgramConfig {
    fn default() -> Self {
        Self { num_mappings: 1, transition_configs: vec![TransitionConfig::default()] }
    }
}

pub struct TransitionConfig {
    pub inputs: usize,
    pub outputs: usize,
    pub arithmetic_instructions: usize,
    pub rw_for_each_mapping: Vec<(usize, usize)>,
    pub should_fail: bool,
}

impl Default for TransitionConfig {
    fn default() -> Self {
        Self {
            inputs: 1,
            outputs: 1,
            arithmetic_instructions: 1,
            rw_for_each_mapping: vec![(1, 1)],
            should_fail: false,
        }
    }
}

pub fn construct_program(config: ProgramConfig, namer: &mut Namer) -> Program<Testnet3> {
    // Construct the program string.
    let mut program_string = format!("program {}.aleo;\n", namer.create_name("program"));
    // Add the desired number of mappings.
    for i in 0..config.num_mappings {
        // Construct the mapping string.
        let mapping_string = format!(
            "mapping map_{}:\n\
            key left as field.public;\n\
            value right as field.public;\n\n",
            i
        );
        program_string.push_str(&mapping_string);
    }
    // TODO: Parameterize.
    program_string.push_str("function foo:\n");

    // Parse the program string.
    Program::from_str(&program_string).unwrap()
}

fn construct_transition_function(config: TransitionConfig, namer: &mut Namer) -> Function<Testnet3> {
    // Construct the empty transition function.
    let mut transition_function = Function::new(Identifier::try_from(namer.create_name("transition")).unwrap());

    todo!();

    transition_function
}
