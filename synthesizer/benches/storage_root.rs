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
    network::Testnet3,
    program::{Identifier, Plaintext, ProgramID, Value},
    types::Group,
};
use snarkvm_synthesizer::{ProgramMemory, ProgramStorage};
use snarkvm_utilities::{TestRng, Uniform};
use std::str::FromStr;

use criterion::Criterion;

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

fn program_memory_storage_root(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    let program_id = ProgramID::<Testnet3>::from_str("benchmark_storage_root.aleo").unwrap();

    let key_value_pairs = sample_key_value_pairs(1000, rng);

    for num_mappings in [10, 100, 1000] {
        for num_key_values in [10, 100, 1000] {
            // Initialize a new program store.
            let program_store = ProgramMemory::<Testnet3>::open(None).unwrap();

            // Insert the key value pairs.
            for mapping_number in 0..num_mappings {
                let mapping_name = Identifier::from_str(&format!("mapping_{}", mapping_number)).unwrap();

                // Initialize the mapping.
                program_store.initialize_mapping(&program_id, &mapping_name).unwrap();

                for (key, value) in key_value_pairs.iter().take(num_key_values) {
                    program_store.insert_key_value(&program_id, &mapping_name, key.clone(), value.clone()).unwrap();
                }
            }

            c.bench_function(
                &format!("Storage root: {} mappings w/ {} key-value pairs", num_mappings, num_key_values),
                move |b| b.iter(|| program_store.get_checksum().unwrap()),
            );
        }
    }
}

criterion_group! {
    name = storage_root;
    config = Criterion::default().sample_size(50);
    targets = program_memory_storage_root
}

criterion_main!(storage_root);
