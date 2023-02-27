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

use anyhow::Result;
use console::{
    network::Testnet3,
    program::{Identifier, Plaintext, ProgramID, Value},
    types::Group,
};
use snarkvm_synthesizer::{ProgramMemory, ProgramStorage};
use snarkvm_utilities::{TestRng, Uniform};
use std::str::FromStr;

fn sample_key_value_pairs(
    num_key_value_pairs: usize,
    rng: &mut TestRng,
) -> Vec<(Plaintext<Testnet3>, Value<Testnet3>)> {
    let mut key_value_pairs = Vec::with_capacity(num_key_value_pairs);

    let value = Value::<Testnet3>::from_str(&format!("{}", Group::<Testnet3>::rand(rng))).unwrap();

    for i in 0..num_key_value_pairs {
        let key = Plaintext::<Testnet3>::from_str(&format!("{i}u32")).unwrap();
        key_value_pairs.push((key, value.clone()));
    }

    key_value_pairs
}

pub fn populate_program_memory(
    program_store: &mut ProgramMemory<Testnet3>,
    parameters: &Vec<Vec<usize>>,
    rng: &mut TestRng,
) -> Result<()> {
    // For each program, initialize its associated state.
    for (i, mapping_sizes) in parameters.iter().enumerate() {
        // Construct the program ID.
        let program_id = ProgramID::<Testnet3>::from_str(&format!("program_{i}.aleo")).unwrap();

        // Initialize each mapping.
        for (j, size) in mapping_sizes.iter().enumerate() {
            // Construct the mapping name.
            let mapping_name = Identifier::from_str(&format!("mapping_{}", j))?;

            // Initialize the mapping.
            program_store.initialize_mapping(&program_id, &mapping_name)?;

            // Sample the key-value pairs.
            let key_value_pairs = sample_key_value_pairs(*size, rng);

            // Insert the key-value pairs.
            for (key, value) in key_value_pairs.iter() {
                program_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone())?;
            }
        }
    }
    Ok(())
}
