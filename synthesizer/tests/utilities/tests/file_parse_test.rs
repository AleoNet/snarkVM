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

/// A test for a parser, where the entire file is the test input.
pub struct FileParseTest {
    path: PathBuf,
    test_string: String,
}

impl FileParseTest {
    /// Returns the test string.
    pub fn test_string(&self) -> &String {
        &self.test_string
    }
}

impl Test for FileParseTest {
    /// Loads the test from a given path.
    fn load<P: AsRef<Path>>(path: P) -> Self {
        let path = path.as_ref().to_path_buf();
        // Read the contents of the test file.
        let test_string = std::fs::read_to_string(&path).expect("Failed to read test file.");
        Self { path, test_string }
    }

    /// Returns the path to the test file.
    fn path(&self) -> PathBuf {
        self.path.clone()
    }
}
