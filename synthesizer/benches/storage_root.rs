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

#[path = "./utilities.rs"]
mod utilities;
use utilities::*;

use console::network::Testnet3;
use snarkvm_synthesizer::{ProgramMemory, ProgramStorage};
use snarkvm_utilities::TestRng;

use criterion::Criterion;

fn program_memory_storage_root(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    for num_mappings in [10, 100, 1000] {
        for num_key_values in [10, 100, 1000] {
            // Initialize a new program store.
            let mut program_store = ProgramMemory::<Testnet3>::open(None).unwrap();

            // Populate the program store.
            let parameters = vec![vec![num_key_values]; num_mappings];
            populate_program_memory(&mut program_store, &parameters, rng).unwrap();

            c.bench_function(
                &format!("Storage root: {} mappings w/ {} key-value pairs", num_mappings, num_key_values),
                move |b| b.iter(|| program_store.get_checksum().unwrap()),
            );
        }
    }
}

// Benchmark the storage root computation over an in-memory program store.
criterion_group! {
    name = storage_root;
    config = Criterion::default().sample_size(50);
    targets = program_memory_storage_root
}

criterion_main!(storage_root);
