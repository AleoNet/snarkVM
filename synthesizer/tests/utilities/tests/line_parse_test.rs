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

use crate::Test;

use std::path::{Path, PathBuf};

/// A set of tests for a parser, where each line is the test input.
pub struct LineParseTest {
    path: PathBuf,
    test_strings: Vec<String>,
}

impl LineParseTest {
    /// Returns the set of test strings to be run.
    pub fn test_strings(&self) -> &Vec<String> {
        &self.test_strings
    }
}

impl Test for LineParseTest {
    /// Loads the tests from a given path.
    fn load<P: AsRef<Path>>(path: P) -> Self {
        let path = path.as_ref().to_path_buf();
        // Read the contents test file.
        let test_strings =
            std::fs::read_to_string(&path).expect("Failed to read test file.").lines().map(|l| l.to_string()).collect();
        Self { path, test_strings }
    }

    /// Returns the path to the test file.
    fn path(&self) -> PathBuf {
        self.path.clone()
    }
}
