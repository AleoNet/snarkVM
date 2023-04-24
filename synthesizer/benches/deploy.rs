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

use std::str::FromStr;
use utilities::*;

use snarkvm_synthesizer::Program;

use criterion::Criterion;

// Note: 32 is the maximum number of mappings that can be included in a single program.
const NUM_MAPPINGS: &[usize] = &[0, 1, 2, 4, 8, 16, 32];
const NUM_DEPLOYMENTS: &[usize] = &[10, 100, 1000, 10000];

#[cfg(feature = "test-utilities")]
fn bench_deployment(c: &mut Criterion) {
    let mut program_string = r"
program test.aleo;"
        .to_string();

    let mut mappings_added = 0;
    for num_mappings in NUM_MAPPINGS {
        // Construct the program.
        for i in mappings_added..*num_mappings {
            program_string.push_str(&format!("mapping map_{i}:key left as field.public;value right as field.public;"));
        }
        let mut final_string = program_string.clone();
        final_string.push_str("function foo:");
        mappings_added = *num_mappings;
        bench_speculate_commit_and_finalize(
            c,
            format!("deploy_with_{num_mappings}_mappings"),
            &[],
            &[],
            &[Program::from_str(&final_string).unwrap()],
            &[],
            &[1],
        );
    }

    program_string.push_str("function foo:");
    bench_speculate_commit_and_finalize(
        c,
        format!("deploy_with_{}_mappings", NUM_MAPPINGS.last().unwrap()),
        &[],
        &[],
        &[Program::from_str(&program_string).unwrap()],
        &[],
        NUM_DEPLOYMENTS,
    );
}

#[cfg(feature = "test-utilities")]
criterion_group! {
    name = deploy;
    config = Criterion::default().sample_size(10);
    targets = bench_deployment
}
#[cfg(feature = "test-utilities")]
criterion_main!(deploy);
