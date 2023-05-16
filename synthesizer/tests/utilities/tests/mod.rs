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

pub mod file_parse_test;
pub use file_parse_test::*;

pub mod line_parse_test;
pub use line_parse_test::*;

use anyhow::Result;
use std::path::Path;
use walkdir::WalkDir;

/// A general interface for a test, with an expected result.
/// The output of the test can be checked against the expected result.
/// The expected result can be saved.
pub trait ExpectedTest: Sized {
    type Test;
    type Output;
    /// Loads the test and expectation from the given path.
    fn load<P: AsRef<Path>>(test_path: P, expectation_dir: P) -> Self;
    /// Checks the expectation against the given output.
    /// Prints an error message if the test case fails.
    fn check(&self, output: &Self::Output) -> Result<()>;
    /// Saves the test output.
    fn save(&self, output: &Self::Output) -> Result<()>;
}

/// Recursively reads all files in the `dir` directory and loads them as tests.
/// Filters the test file names by the `TEST_FILTER` environment variable.
/// Note that `dir` must be a relative path from `[...]/snarkVM/synthesizer/tests`.
pub fn load_tests<P: AsRef<Path>, T: ExpectedTest>(test_dir: P, expectation_dir: P) -> Vec<T> {
    let test_dir =
        std::env::current_dir().expect("Failed to retrieve the current directory.").join("tests").join(test_dir);
    // Read the `TEST_FILTER` environment variable.
    let test_filter = std::env::var("TEST_FILTER").ok();
    // Recursively read all files in the `root` directory, filtering out directories and files without sufficient permissions.
    let paths =
        WalkDir::new(test_dir).into_iter().filter_map(|e| e.ok()).map(|e| e.into_path()).filter(|path| path.is_file());
    // Filter the test file names by the `TEST_FILTER` environment variable.
    let filtered_paths = match test_filter {
        Some(ref filter) => paths
            .filter(|path| {
                path.file_name()
                    .expect("Failed to get filename.")
                    .to_str()
                    .expect("Filename is not valid Unicode.")
                    .contains(filter)
            })
            .collect::<Vec<_>>(),
        None => paths.collect::<Vec<_>>(),
    };
    // Initialize the test files.
    filtered_paths
        .into_iter()
        .map(|test_path| T::load(test_path, expectation_dir.as_ref().to_path_buf()))
        .collect::<Vec<_>>()
}
