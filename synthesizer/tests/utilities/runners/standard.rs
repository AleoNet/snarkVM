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

use crate::utilities::load_tests;
use std::path::Path;
use walkdir::WalkDir;

/// A `StandardRunner` walks the test directory, loads the tests, and runs them in order.
pub struct StandardRunner<T: Test<Config = ()>> {
    tests: Vec<T>,
}

impl<T: Test<Config = ()>> StandardRunner<T> {
    /// Initializes the test runner.
    pub fn initialize<P: AsRef<Path>>(dir: P) -> Self {
        // Initialize the test files.
        let tests = load_tests(dir);
        Self { tests }
    }

    /// Runs all tests.
    pub fn run(&self) {
        for test in &self.tests {
            test.run(&());
        }
    }
}
