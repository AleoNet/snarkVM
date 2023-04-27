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

// #![cfg(feature = "test-utilities")]
//
// #[macro_use]
// extern crate criterion;
//
// mod utilities;
// use utilities::*;
//
// use console::{network::Testnet3};
// use snarkvm_synthesizer::Program;
//
// use criterion::Criterion;
// use itertools::Itertools;
// use std::str::FromStr;
//
// // Note: 32 is the maximum number of mappings that can be included in a single program.
// const NUM_MAPPINGS: &[usize] = &[0, 1, 2, 4, 8, 16, 32];
// const NUM_DEPLOYMENTS: &[usize] = &[10, 100, 1000, 10000];
//
// /// A helper to construct benchmark programs.
// fn construct_program(i: usize, num_mappings: usize) -> Program<Testnet3> {
//     // Define the fixed portion of the program.
//     let mut program_string = format!(r"
// program deploy_{i}.aleo;
// "
//     );
//     // Add the desired number of mappings.
//     for i in 0..num_mappings {
//         program_string.push_str(&format!("map_{i};key left as field.public;value right as field.public;"));
//     }
//     // Add a dummy function.
//     program_string.push_str("function foo:");
//     Program::from_str(&program_string).unwrap()
// }
//
// fn bench_one_deployment(c: &mut Criterion) {
//     for num_mappings in NUM_MAPPINGS {
//         // Construct the program.
//         let program = construct_program(0, *num_mappings);
//         // Bench the deployment.
//         bench_all(
//             c,
//             &format!("deploy/1_program/{num_mappings}_mappings"),
//             &[],
//             &[],
//             &[program],
//             &[],
//         );
//     }
// }
//
// fn bench_multiple_deployments(c: &mut Criterion) {
//     for num_deployments in NUM_DEPLOYMENTS {
//         // Construct the programs.
//         let programs = (0..*num_deployments).map(|i| construct_program(i, *NUM_MAPPINGS.last().unwrap())).collect_vec();
//         // Bench the deployments.
//         bench_all(
//             c,
//             &format!("deploy/{num_deployments}_programs/{}_mappings", NUM_MAPPINGS.last().unwrap()),
//             &[],
//             &[],
//             &programs,
//             &[],
//         );
//     }
// }
//
// criterion_group! {
//     name = deploy;
//     config = Criterion::default().sample_size(10);
//     targets = bench_one_deployment, bench_multiple_deployments
// }
// criterion_main!(deploy);
