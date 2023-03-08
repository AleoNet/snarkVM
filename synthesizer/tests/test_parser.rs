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

use snarkvm_synthesizer::{Instruction, Program};

use console::network::{prelude::*, Testnet3};

use std::{
    marker::PhantomData,
    path::{Path, PathBuf},
};

pub type FileParserTest<F> = ParserTest<F, 0>;
pub type LineParserTest<F> = ParserTest<F, 1>;

pub struct ParserTest<F: Parser, const PARSE_MODE: u8> {
    path: PathBuf,
    input: String,
    expectation: Option<String>,
    phantom: PhantomData<F>,
}

impl<F: Parser, const PARSE_MODE: u8> Test for ParserTest<F, PARSE_MODE> {
    fn load<P: AsRef<Path>>(path: P) -> Result<Self> {
        // Read the test file.
        let input = std::fs::read_to_string(&path).expect("Failed to read input file.");
        // Load the expectation file.
        let expectation = load_expectation(&path);

        Ok(Self { path: path.as_ref().to_path_buf(), input, expectation, phantom: Default::default() })
    }

    fn run(&self) {
        // A helper to run the parser and convert the result into a readable format.
        let run_parser = |input: &str| {
            // Run the desired parser.
            let result = F::parse(input);
            // Convert the result into a readable format.
            convert_result(result, input)
        };
        let output = match PARSE_MODE {
            // If the `PARSE_MODE` is 0, then run the test on the entire input.
            0 => run_parser(&self.input),
            // If the `PARSE_MODE` is 1, then run the test on each line of the input.
            1 => self.input.lines().map(|line| run_parser(line)).collect::<Vec<_>>().join("\n"),
            _ => panic!("PARSE_MODE must be 0 or 1."),
        };
        // Check the result against the expectation.
        check_and_log_expectation(&self.path, &self.expectation, &output);
    }
}

#[test]
fn test_program_parser() {
    let runner = Runner::<FileParserTest<Program<Testnet3>>>::initialize("./tests/parser/program");
    runner.run();
}

#[test]
fn test_instruction_parser() {
    let runner = Runner::<LineParserTest<Instruction<Testnet3>>>::initialize("./tests/parser/instruction");
    runner.run();
}
