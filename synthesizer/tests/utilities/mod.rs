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

/// This module defines a set of utilities for testing Aleo programs.
///
/// Users define tests in the `tests/tests` directory, and the expected output in the `tests/expectations` directory.
/// Users should separate their tests into different files, and name the expectation files with the same name as the test files.
/// Tests should also be separated into different directories depending on the type of test.
///
/// When the `TEST_FILTER` environment variable is set, then only the tests whose filenames match the filter are run.
/// When the `REWRITE_EXPECTATIONS` environment variable is set, then the expectation files are rewritten.
/// Otherwise, the output is compared against the expectation files.
pub mod expectations;
pub use expectations::*;

pub mod runners;
pub use runners::*;

use console::network::prelude::*;

use std::{
    env::current_dir,
    path::{Path, PathBuf},
};
use walkdir::WalkDir;

/// A general interface for a test.
pub trait Test: Sized {
    /// Loads the test from the given path.
    fn load<P: AsRef<Path>>(input: P) -> Result<Self>;

    /// Runs the test.
    fn run(&self);
}

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
