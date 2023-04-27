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
// use std::iter;
// use std::str::FromStr;
//
// // Note: The number of commands that can be included in a finalize block must be within the range [1, 255].
// const NUM_COMMANDS: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128, 255];
// const NUM_EXECUTIONS: &[usize] = &[2, 4, 8, 16, 32, 64, 128, 256];
// const NUM_PROGRAMS: &[usize] = &[2, 4, 8, 16, 32, 64, 128, 255];
//
// /// A helper to construct benchmark programs.
// fn construct_program(i: usize, num_commands: usize) -> Program<Testnet3> {
//     // Define the fixed portion of the program.
//     let mut program_string = format!(r"
// program get_{i}.aleo;
// mapping balances:
//     key left as field.public;
//     value right as field.public;
// function initialize:
//     finalize;
// finalize initialize:
//     set 0field into balances[0field];
// function getter:
//     finalize;
// finalize getter:
// "
//     );
//     // Add the desired number of commands.
//     for i in 0..num_commands {
//         program_string.push_str(&format!("get balances[0field] into r{i};"));
//     }
//     Program::from_str(&program_string).unwrap()
// }
//
// fn bench_one_execution(c: &mut Criterion) {
//     for num_commands in NUM_COMMANDS {
//         // Construct the program.
//         let program = construct_program(0, *num_commands);
//         // Bench the execution.
//         bench_all(
//             c,
//             &format!("get/1_program/1_execution/{num_commands}_commands"),
//             &[program],
//             &[("get_0.aleo".to_string(), "initialize".to_string(), vec![])],
//             &[],
//             &[("get_0.aleo".to_string(), "getter".to_string(), vec![])],
//         );
//     }
// }
//
// fn bench_multiple_executions(c: &mut Criterion) {
//     for num_executions in NUM_EXECUTIONS {
//         // Construct the program.
//         let program = construct_program(0, *NUM_COMMANDS.last().unwrap());
//         // Construct the executions.
//         let executions = iter::repeat(("get_0.aleo".to_string(), "getter".to_string(), vec![]))
//             .take(*num_executions)
//             .collect_vec();
//         // Bench the execution.
//         bench_all(
//             c,
//             &format!("get/1_program/{num_executions}_executions/{}_commands", NUM_COMMANDS.last().unwrap()),
//             &[program],
//             &[("get_0.aleo".to_string(), "initialize".to_string(), vec![])],
//             &[],
//             &executions,
//         );
//     }
// }
//
// fn bench_multiple_executions_of_multiple_programs(c: &mut Criterion) {
//     for num_programs in NUM_PROGRAMS {
//         // Construct the programs.
//         let initial_deployments = (0..*num_programs).map(|i| construct_program(i, *NUM_COMMANDS.last().unwrap())).collect_vec();
//         // Construct the initial executions.
//         let initial_executions = (0..*num_programs)
//             .map(|i| (format!("get_{i}.aleo"), "initialize".to_string(), vec![]))
//             .collect_vec();
//         // Construct the executions.
//         let mut executions = Vec::with_capacity(num_programs * *NUM_EXECUTIONS.last().unwrap());
//         for _ in 0..*NUM_EXECUTIONS.last().unwrap() {
//             for i in 0..*num_programs {
//                 executions.push((format!("get_{i}.aleo"), "getter".to_string(), vec![]));
//             }
//         }
//         // Bench the execution.
//         bench_all(
//             c,
//             &format!("get/{num_programs}_programs/{}_executions/{}_commands", NUM_EXECUTIONS.last().unwrap(), NUM_COMMANDS.last().unwrap()),
//             &initial_deployments,
//             &initial_executions,
//             &[],
//             &executions,
//         );
//     }
//
// }
//
// criterion_group! {
//     name = benchmarks;
//     config = Criterion::default().sample_size(10);
//     targets = bench_one_execution, bench_multiple_executions,
// }
// criterion_group! {
//     name = long_benchmarks;
//     config = Criterion::default().sample_size(10);
//     targets = bench_multiple_executions_of_multiple_programs
// }
// #[cfg(all(feature="test-utilities", feature="long-benchmarks"))]
// criterion_main!(long_benchmarks);
// #[cfg(all(feature="test-utilities", not(any(feature="long-benchmarks"))))]
// criterion_main!(benchmarks);
