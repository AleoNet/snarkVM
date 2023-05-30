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

use console::program::{Identifier, Value};
use snarkvm_synthesizer::Program;

use anyhow::{bail, Result};
use itertools::Itertools;
use serde_yaml::Sequence;
use std::{
    path::{Path, PathBuf},
    str::FromStr,
};

// TODO: Handle tests where the execution panics or fails.
//  One approach is to create an enum `ExpectedOutput` which can be `Ok(Vec<Value>)` or `Err(String)`.

/// A test for a program, containing the program definition and a set of test cases.
pub struct ProgramTest {
    test_program: Program<CurrentNetwork>,
    test_cases: Vec<(Identifier<CurrentNetwork>, Vec<Value<CurrentNetwork>>)>,
    expected_results: Vec<Vec<Value<CurrentNetwork>>>,
    expectation_path: PathBuf,
    rewrite: bool,
}

impl ProgramTest {
    /// Returns the test program.
    pub fn test_program(&self) -> &Program<CurrentNetwork> {
        &self.test_program
    }

    /// Returns the test cases.
    pub fn test_cases(&self) -> &[(Identifier<CurrentNetwork>, Vec<Value<CurrentNetwork>>)] {
        &self.test_cases
    }
}

impl ExpectedTest for ProgramTest {
    type Output = Vec<Vec<Value<CurrentNetwork>>>;
    type Test = Vec<Vec<Value<CurrentNetwork>>>;

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
        // Parse the comment into a sequence of test cases.
        let test_cases = serde_yaml::from_str::<Sequence>(comment)
            .expect("invalid test configuration")
            .into_iter()
            .map(|value| {
                let value = value.as_sequence().expect("invalid test case");
                let (function_name, args) =
                    value.split_first().expect("test case must specify the function name and arguments");
                let function_name = Identifier::<CurrentNetwork>::from_str(
                    function_name.as_str().expect("function name must be a string"),
                )
                .expect("function name must be an identifier");
                let args = args
                    .iter()
                    .map(|value| {
                        Value::<CurrentNetwork>::from_str(value.as_str().expect("argument must be a string"))
                            .expect("argument must be a value")
                    })
                    .collect_vec();
                (function_name, args)
            })
            .collect_vec();
        // Parse the remainder of the test file into a program.
        let test_program =
            Program::<CurrentNetwork>::from_str(&source[first_comment_start + 2 + end_first_comment + 2..])
                .expect("Failed to parse program.");
        // Construct the path the expectation file.
        let expectation_path = get_expectation_path(&test_path, &expectation_dir);
        // If the expectation file should be rewritten, then there is no need to read the expectation file.
        let expected_results = match rewrite {
            true => vec![],
            false => {
                let source = std::fs::read_to_string(&expectation_path).expect("Failed to read expectation file.");
                serde_yaml::from_str::<Sequence>(&source)
                    .expect("invalid expectation")
                    .into_iter()
                    .map(|value| {
                        let value = value.as_sequence().expect("invalid expectation case");
                        value
                            .iter()
                            .map(|value| {
                                Value::<CurrentNetwork>::from_str(value.as_str().expect("expected must be a string"))
                                    .expect("expected must be a value")
                            })
                            .collect_vec()
                    })
                    .collect_vec()
            }
        };
        Self { test_program, test_cases, expected_results, expectation_path, rewrite }
    }

    fn check(&self, output: &Self::Output) -> Result<()> {
        // Initialize space to accumulate errors.
        let mut errors = Vec::new();
        // If the expectation file should be rewritten, then there is no need to check the output.
        if !self.rewrite {
            self.test_cases.iter().zip_eq(self.expected_results.iter().zip_eq(output.iter())).for_each(
                |((function_name, args), (expected, actual))| {
                    if expected != actual {
                        let mut test = format!("Function: {}\nInputs: ", function_name);
                        test.push_str(&args.iter().map(|value| value.to_string()).join(", "));
                        let expected = expected.iter().map(|value| value.to_string()).join(",");
                        let actual = actual.iter().map(|value| value.to_string()).join(",");
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
            let output = serde_yaml::Value::Sequence(
                output
                    .iter()
                    .map(|values| {
                        serde_yaml::Value::Sequence(
                            values
                                .iter()
                                .map(|value| serde_yaml::Value::String(value.to_string()))
                                .collect::<Sequence>(),
                        )
                    })
                    .collect::<Sequence>(),
            );
            std::fs::write(
                &self.expectation_path,
                serde_yaml::to_string(&output).expect("failed to serialize output to string"),
            )?;
        }
        Ok(())
    }
}
