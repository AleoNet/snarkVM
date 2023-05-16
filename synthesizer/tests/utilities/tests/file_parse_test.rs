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

use crate::{get_expectation_path, print_difference, ExpectedTest};

use anyhow::{bail, Result};
use std::path::{Path, PathBuf};

/// A test for a parser, where the entire file is the test input.
pub struct FileParseTest {
    test_string: String,
    expectation: String,
    expectation_path: PathBuf,
    rewrite: bool,
}

impl FileParseTest {
    /// Returns the test string.
    pub fn test_string(&self) -> &String {
        &self.test_string
    }
}

impl ExpectedTest for FileParseTest {
    type Output = String;
    type Test = String;

    /// Loads the test from a given path.
    fn load<P: AsRef<Path>>(test_path: P, expectation_dir: P) -> Self {
        // Read the contents of the test file.
        let test_string = std::fs::read_to_string(&test_path).expect("Failed to read test file.");
        // Check if the expectation file should be rewritten.
        let rewrite = std::env::var("REWRITE_EXPECTATIONS").is_ok();
        // Construct the path the expectation file.
        let expectation_path = get_expectation_path(&test_path, &expectation_dir);
        // If the expectation file should be rewritten, then there is no need to read the expectation file.
        let expectation = match rewrite {
            true => String::new(),
            false => std::fs::read_to_string(&expectation_path).expect("Failed to read expectation file."),
        };
        Self { test_string, expectation, expectation_path, rewrite }
    }

    fn check(&self, output: &Self::Output) -> Result<()> {
        match self.rewrite {
            false if self.expectation != *output => {
                bail!("{}", print_difference(&self.test_string, &self.expectation, output))
            }
            _ => Ok(()),
        }
    }

    fn save(&self, output: &Self::Output) -> Result<()> {
        if self.rewrite {
            std::fs::write(&self.expectation_path, output)?;
        }
        Ok(())
    }
}
