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

use std::{
    env::current_dir,
    fmt::Display,
    path::{Path, PathBuf},
};

/// Constructs the path to the expectation file corresponding to the given test file.
pub fn get_expectation_path<P: AsRef<Path>>(test_path: P, expectation_dir: P) -> PathBuf {
    // Get the current directory.
    let current_dir = current_dir().expect("Failed to get current directory.");
    // Construct the path to the directory containing the expectation file.
    let expectation_dir = current_dir.join("tests").join(expectation_dir);
    // Construct the path to the expectation file.
    expectation_dir.join(Path::new(test_path.as_ref().file_name().unwrap()).with_extension("out"))
}

/// Helper function to print the difference between the expected and actual output.
pub fn print_difference(test: impl Display, expected: impl Display, actual: impl Display) -> String {
    let mut message = r"
============================================================
TEST
------------------------------------------------------------
"
    .to_string();
    message.push_str(&test.to_string());
    message.push_str(
        r"

============================================================
EXPECTED
------------------------------------------------------------
",
    );
    message.push_str(&expected.to_string());
    message.push_str(
        r"

============================================================
ACTUAL
------------------------------------------------------------
",
    );
    message.push_str(&actual.to_string());
    message.push_str(
        r"
============================================================

",
    );
    message
}
