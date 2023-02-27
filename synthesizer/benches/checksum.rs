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

use anyhow::Result;
use console::network::Testnet3;
use snarkvm_utilities::{TestRng, ToBits};
use std::iter;

use console::{
    prelude::{Network, Zero},
    types::Field,
};
use criterion::Criterion;
use snarkvm_synthesizer::{helpers::MapRead, ProgramMemory, ProgramStorage};

// A helper function to lazily prepare the input for the checksum computation.
// This function avoids constructing the entire input in memory, which is useful in benchmarking the raw performance of the checksum.
fn prepare_bit_streams(parameters: &[usize]) -> impl Iterator<Item = impl Iterator<Item = bool>> + '_ {
    parameters.iter().map(move |mapping_size_in_bits| {
        let mapping_id = Field::<Testnet3>::zero();
        mapping_id.to_bits_le().into_iter().chain(iter::repeat(false).take(*mapping_size_in_bits))
    })
}

// A helper function to run the benchmark, parameterized by the outer and inner hash functions.
fn run_checksum_benchmark(
    parameters: &[usize],
    outer: fn(&[bool]) -> Result<Field<Testnet3>>,
    inner: fn(&[bool]) -> Result<Field<Testnet3>>,
) {
    let input = prepare_bit_streams(parameters);
    let mapping_checksums = input.map(|bits| {
        // Compute the mapping checksum as `Hash( bits )`.
        let mapping_checksum = inner(&bits.collect::<Vec<_>>()).expect("Could not compute mapping checksum");
        // Return the bits of the mapping checksum.
        mapping_checksum.to_bits_le()
    });
    // Compute the storage root as `Hash( mapping_checksums )`.
    outer(&mapping_checksums.flatten().collect::<Vec<_>>()).expect("Could not compute storage root");
}

fn compare_checksums_by_hash_function(c: &mut Criterion) {
    let mut group = c.benchmark_group("Compare Checksums by Inner and Outer Hash Functions");

    for i in 24..31 {
        // Initialize parameters corresponding to the number and size of the mappings.
        let parameters = [1 << i];

        // Benchmark BHP256(BHP256).
        group.bench_with_input(format!("BHP256(BHP256): {} bits", 1 << i), &parameters, |b, parameters| {
            b.iter(|| run_checksum_benchmark(parameters, Testnet3::hash_bhp256, Testnet3::hash_bhp256))
        });
        // Benchmark BHP512(BHP512).
        group.bench_with_input(format!("BHP512(BHP512): {} bits", 1 << i), &parameters, |b, parameters| {
            b.iter(|| run_checksum_benchmark(parameters, Testnet3::hash_bhp512, Testnet3::hash_bhp512))
        });
        // Benchmark BHP768(BHP768).
        group.bench_with_input(format!("BHP768(BHP768): {} bits", 1 << i), &parameters, |b, parameters| {
            b.iter(|| run_checksum_benchmark(parameters, Testnet3::hash_bhp768, Testnet3::hash_bhp768))
        });
        // Benchmark BHP1024(BHP1024).
        group.bench_with_input(format!("BHP1024(BHP1024): {} bits", 1 << i), &parameters, |b, parameters| {
            b.iter(|| run_checksum_benchmark(parameters, Testnet3::hash_bhp1024, Testnet3::hash_bhp1024))
        });
    }

    group.finish()
}

fn compare_checksum_and_storage_root(c: &mut Criterion) {
    let mut group = c.benchmark_group("Compare Checksum and Storage Root");

    // Initialize the rng.
    let rng = &mut TestRng::default();

    for i in 10..20 {
        // Initialize the program memory.
        let mut program_store = ProgramMemory::<Testnet3>::open(None).unwrap();

        // Populate the program store.
        let parameters = vec![vec![1 << i]; 1];
        populate_program_memory(&mut program_store, &parameters, rng).unwrap();

        // Calculate the size of the program store in bits.
        let program_store_size_in_bits = program_store
            .key_value_id_map()
            .iter()
            .map(|(mapping_id, key_value_ids)| {
                mapping_id.to_bits_le().len()
                    + key_value_ids.values().map(|value_id| value_id.to_bits_le().len()).sum::<usize>()
            })
            .sum();

        // Benchmark the storage root computation.
        group.bench_function(&format!("Storage root: 1 mapping w/ {} key-value pairs", 1 << i), move |b| {
            b.iter(|| program_store.get_checksum().unwrap())
        });

        // Benchmark the checksum computation.
        group.bench_with_input(
            format!("Checksum: {} bits", program_store_size_in_bits),
            &[program_store_size_in_bits],
            |b, parameters| {
                b.iter(|| run_checksum_benchmark(parameters, Testnet3::hash_bhp1024, Testnet3::hash_bhp1024))
            },
        );
    }

    group.finish()
}

// Benchmark the checksum computation over a stream of bits.
criterion_group! {
    name = checksum;
    config = Criterion::default().sample_size(10);
    targets = compare_checksums_by_hash_function, compare_checksum_and_storage_root
}

criterion_main!(checksum);
