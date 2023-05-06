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

pub mod multiple;
pub use multiple::*;

pub mod single;
pub use single::*;

use console::network::Network;
use snarkvm_synthesizer::Program;

use std::str::FromStr;

/// A helper to construct benchmark programs.
pub(crate) fn construct_program<N: Network>(i: usize, num_mappings: usize) -> Program<N> {
    // Define the fixed portion of the program.
    let mut program_string = format!(
        r"
program deploy_{num_mappings}_{i}.aleo;
"
    );
    // Add the desired number of mappings.
    for i in 0..num_mappings {
        program_string.push_str(&format!("map_{i};key left as field.public;value right as field.public;"));
    }
    // Add a dummy function.
    program_string.push_str("function foo:");
    Program::from_str(&program_string).unwrap()
}
