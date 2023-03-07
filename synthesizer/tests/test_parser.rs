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

mod utilities;
use utilities::*;

use snarkvm_synthesizer::Program;

use console::network::{prelude::*, Testnet3};

use std::{
    marker::PhantomData,
    path::{Path, PathBuf},
};

struct ParserTest<F: Parser> {
    path: PathBuf,
    input: String,
    expectation: Option<String>,
    phantom: PhantomData<F>,
}

impl<F: Parser> Test for ParserTest<F> {
    fn load<P: AsRef<Path>>(path: P) -> Result<Self> {
        // Read the test file.
        let input = std::fs::read_to_string(&path).expect("Failed to read input file.");
        // If the `REWRITE_EXPECTATIONS` environment variable is not set, then read the expectation file.
        let expectation = match std::env::var("REWRITE_EXPECTATIONS").is_ok() {
            true => None,
            false => {
                let current_dir = std::env::current_dir().expect("Failed to get current directory.");
                let tests_dir = current_dir.join("tests/tests");
                let expectations_dir = current_dir.join("tests/expectations");
                let expectation_path =
                    expectations_dir.join(path.as_ref().strip_prefix(&tests_dir).unwrap().with_extension("out"));
                let expectation = std::fs::read_to_string(expectation_path).expect("Failed to read expectation file.");
                Some(expectation)
            }
        };

        Ok(Self { path: path.as_ref().to_path_buf(), input, expectation, phantom: Default::default() })
    }

    fn run(&self) {
        let output = F::parse(&self.input);
        let output_string = convert_result(output, &self.input);
        match &self.expectation {
            // If the `REWRITE_EXPECTATIONS` environment variable is set, then rewrite the expectation file.
            None => {
                let current_dir = std::env::current_dir().expect("Failed to get current directory.");
                let tests_dir = current_dir.join("tests/tests");
                let expectations_dir = current_dir.join("tests/expectations");
                let expectation_path =
                    expectations_dir.join(self.path.strip_prefix(&tests_dir).unwrap().with_extension("out"));

                std::fs::write(expectation_path, output_string).expect("Failed to write expectations.");
            }
            // Otherwise check the output against the expectation.
            Some(expectation) => {
                if expectation != &output_string {
                    eprintln!("Expected:\n{}\nGot:\n{}\n", expectation, output_string)
                }
            }
        }
    }
}

#[test]
fn test_program_parser() {
    let runner = Runner::<ParserTest<Program<Testnet3>>>::initialize("./tests/parser/program");
    runner.run();
}
