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

use super::*;

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

/// Loads the expectation file if `REWRITE_EXPECTATIONS` is not set.
pub fn load_expectation<P: AsRef<Path>>(path: P) -> Option<String> {
    // If the `REWRITE_EXPECTATIONS` environment variable is not set, then read the expectation file.
    match std::env::var("REWRITE_EXPECTATIONS").is_ok() {
        true => None,
        false => {
            let expectation_path = get_expectation_path(path);
            let expectation = std::fs::read_to_string(expectation_path).expect("Failed to read expectation file.");
            Some(expectation)
        }
    }
}

/// If `REWRITE_EXPECTATIONS` is set, then rewrite the expectation file.
/// Otherwise, check the output against the expectation.
pub fn check_and_log_expectation<P: AsRef<Path>>(path: P, expectation: &Option<String>, output: &str) {
    match expectation {
        // If the `REWRITE_EXPECTATIONS` environment variable is set, then rewrite the expectation file.
        None => {
            let expectation_path = get_expectation_path(path);
            std::fs::write(expectation_path, output).expect("Failed to write expectations.");
        }
        // Otherwise check the output against the expectation.
        Some(expectation) => {
            assert_eq!(expectation, output);
        }
    }
}
