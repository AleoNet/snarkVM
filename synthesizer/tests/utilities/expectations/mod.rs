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

pub mod file_expectation;
pub use file_expectation::*;

pub mod line_expectation;
pub use line_expectation::*;

use anyhow::{bail, Result};
use itertools::Itertools;
use std::{
    env::current_dir,
    path::{Path, PathBuf},
};

/// A general interface for an expectation.
pub trait Expectation: Sized {
    type Test;
    type Output;

    /// Loads the expectation from the given path.
    fn load<P: AsRef<Path>>(input: P) -> Result<Self>;

    /// Checks the expectation against the given output.
    fn check(&self, test: &Self::Test, output: &Self::Output) -> Result<()>;

    /// Saves the test output.
    fn save(&self, output: &Self::Output) -> Result<()>;
}

/// Constructs the path to the expectation file corresponding to the given test file.
pub fn get_expectation_path<P: AsRef<Path>>(test_path: P) -> PathBuf {
    // Get the current directory.
    let current_dir = current_dir().expect("Failed to get current directory.");
    // Construct the path to the expectations directory.
    let expectations_dir = current_dir.join("tests/expectations");
    // Construct the path to the test directory.
    let tests_dir = current_dir.join("tests/tests");
    // Construct the path to the expectation file.
    expectations_dir.join(test_path.as_ref().to_path_buf().strip_prefix(tests_dir).unwrap().with_extension("out"))
}

/// Helper function to print the difference between the expected and actual output.
pub fn print_difference(test: &str, expected: &str, actual: &str) -> String {
    let mut message = r"
============================================================
TEST
------------------------------------------------------------
"
    .to_string();
    message.push_str(test);
    message.push_str(
        r"

============================================================
EXPECTED
------------------------------------------------------------
",
    );
    message.push_str(expected);
    message.push_str(
        r"

============================================================
ACTUAL
------------------------------------------------------------
",
    );
    message.push_str(actual);
    message.push_str(
        r"
============================================================

",
    );
    message
}
