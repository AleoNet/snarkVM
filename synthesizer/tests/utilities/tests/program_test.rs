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

use crate::{get_expectation_path, print_difference, CurrentNetwork, ExpectedTest};

use console::{account::PrivateKey, program::Identifier};
use snarkvm_synthesizer::program::Program;

use anyhow::{bail, Result};
use itertools::Itertools;
use serde_yaml::{Mapping, Sequence, Value};
use std::{
    path::{Path, PathBuf},
    str::FromStr,
};

// TODO: Handle tests where the execution panics or fails.
//  One approach is to create an enum `ExpectedOutput` which can be `Ok(Vec<Value>)` or `Err(String)`.

/// A test for a program, containing the program definition, an optional seed for the RNG, and a set of test cases.
// Note: We use YAML for `cases` and `expected` to allow for flexible definitions across various types of tests.
pub struct ProgramTest {
    /// The program.
    program: Program<CurrentNetwork>,
    /// The set of test cases.
    cases: Vec<Value>,
    /// The set of expected outputs for each test case.
    expected: Vec<Value>,
    /// The path to the expectation file.
    path: PathBuf,
    /// Whether the expectation file should be rewritten.
    rewrite: bool,
    /// The seed for the RNG.
    randomness: Option<u64>,
}

impl ProgramTest {
    /// Returns the program.
    pub fn program(&self) -> &Program<CurrentNetwork> {
        &self.program
    }

    /// Returns the test cases.
    pub fn cases(&self) -> &[Value] {
        &self.cases
    }

    /// Returns the optional seed for the RNG.
    pub fn randomness(&self) -> Option<u64> {
        self.randomness
    }
}

impl ExpectedTest for ProgramTest {
    type Output = Vec<Value>;
    type Test = Vec<Value>;

    /// Loads the test from a given path.
    fn load<P: AsRef<Path>>(test_path: P, expectation_dir: P) -> Self {
        // Check if the expectation file should be rewritten.
        let rewrite = std::env::var("REWRITE_EXPECTATIONS").is_ok();

        // Read the contents of the test file.
        let source = std::fs::read_to_string(&test_path).expect("Failed to read test file.");

        // Parse out the first comment, denoted by `/* ... */`.
        let first_comment_start = source.find("/*").expect("test file must contain a comment");
        let end_first_comment = source[first_comment_start + 2..].find("*/").expect("test file must contain a comment");
        let comment = &source[first_comment_start + 2..first_comment_start + 2 + end_first_comment];

        // Parse the comment into the test configuration.
        let test_config = serde_yaml::from_str::<Mapping>(comment).expect("invalid test configuration");

        // If the `randomness` field is present in the config, parse it as a `u64`.
        let randomness = test_config.get("randomness").map(|value| value.as_u64().expect("`randomness` must be a u64"));

        // Extract the test cases from the config.
        let cases = test_config
            .get("cases")
            .expect("configuration must contain `cases`")
            .as_sequence()
            .expect("cases must be a sequence")
            .clone();

        // Parse the remainder of the test file into a program.
        let program = Program::<CurrentNetwork>::from_str(&source[first_comment_start + 2 + end_first_comment + 2..])
            .expect("Failed to parse program.");

        // Construct the path to the expectation file.
        let path = get_expectation_path(&test_path, &expectation_dir);
        // If the expectation file should be rewritten, then there is no need to read the expectation file.
        let expected = match rewrite {
            true => vec![],
            false => {
                let source = std::fs::read_to_string(&path).expect("Failed to read expectation file.");
                serde_yaml::from_str::<Sequence>(&source).expect("invalid expectation")
            }
        };

        Self { program, cases, expected, path, rewrite, randomness }
    }

    fn check(&self, output: &Self::Output) -> Result<()> {
        // Initialize space to accumulate errors.
        let mut errors = Vec::new();
        // If the expectation file should be rewritten, then there is no need to check the output.
        if !self.rewrite {
            self.cases.iter().zip_eq(self.expected.iter().zip_eq(output.iter())).for_each(
                |(test, (expected, actual))| {
                    if expected != actual {
                        let test = serde_yaml::to_string(test).expect("failed to serialize test to string");
                        let expected =
                            serde_yaml::to_string(expected).expect("failed to serialize expected output to string");
                        let actual =
                            serde_yaml::to_string(actual).expect("failed to serialize actual output to string");
                        errors.push(print_difference(test, expected, actual));
                    }
                },
            );
        };
        // Write the errors, if any.
        match errors.is_empty() {
            true => Ok(()),
            false => bail!("{}", errors.iter().join("\n\n")),
        }
    }

    fn save(&self, output: &Self::Output) -> Result<()> {
        if self.rewrite {
            std::fs::write(&self.path, serde_yaml::to_string(&output).expect("failed to serialize output to string"))?;
        }
        Ok(())
    }
}
