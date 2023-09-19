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

mod utilities;
use utilities::*;

use std::fmt::Write;

use console::network::prelude::*;
use synthesizer_process::Process;
use synthesizer_program::Program;

#[test]
fn test_process_add_program() {
    // Initialize a vector of programs.
    let mut programs = Vec::new();

    // Load the programs from `./tests/tests/process_add_program`.
    let current_dir = std::env::current_dir().unwrap();
    for entry in std::fs::read_dir(current_dir.join("./tests/tests/process_add_program")).unwrap() {
        let path = entry.unwrap().path();
        programs.push(Program::<CurrentNetwork>::from_str(std::fs::read_to_string(path).unwrap().as_str()).unwrap());
    }
    // Load the programs from `./tests/tests/parser/program`.
    programs.extend(
        load_tests::<_, FileParseTest>("./tests/parser/program", "./expectations/parser/program")
            .iter()
            .filter_map(|test| Program::from_str(test.test_string()).ok()),
    );
    // Load the programs from `./tests/tests/process/execute`.
    programs.extend(
        load_tests::<_, ProgramTest>("./tests/process/execute", "./expectations/process/process/execute")
            .into_iter()
            .flat_map(|test| test.programs().to_vec()),
    );
    // Load the programs from `./tests/tests/vm/execute_and_finalize`.
    programs.extend(
        load_tests::<_, ProgramTest>("./tests/vm/execute_and_finalize", "./expectations/vm/execute_and_finalize")
            .into_iter()
            .flat_map(|test| test.programs().to_vec()),
    );

    // Initialize a process.
    let mut process = Process::<CurrentNetwork>::load().unwrap();

    // Initialize the output string.
    let mut output = String::new();

    // Add each program to the process.
    programs.iter().for_each(|program| match process.add_program(program) {
        Ok(_) => writeln!(output, "Successfully added {}.", program.id()).unwrap(),
        Err(err) => writeln!(output, "Failed to add {}: {err}", program.id()).unwrap(),
    });

    // If the `REWRITE_EXPECTATIONS` environment variable is set, overwrite the expectations.
    // Otherwise, load the expectations and compare them against the output.
    let path_to_expectations = current_dir.join("./tests/expectations/process_add_program.out");
    match std::env::var("REWRITE_EXPECTATIONS").is_ok() {
        true => std::fs::write(path_to_expectations, output).unwrap(),
        false => assert_eq!(output, std::fs::read_to_string(path_to_expectations).unwrap()),
    }
}
