// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::prelude::{Network, ProgramID};
use snarkvm_compiler::Program;

use anyhow::{ensure, Result};
use std::{
    fs::File,
    io::Write,
    path::{Path, PathBuf},
};

pub struct README {
    /// The file path.
    path: PathBuf,
}

impl README {
    /// Creates a new README file with the given directory path and program ID.
    pub fn create<N: Network>(directory: &Path, id: &ProgramID<N>) -> Result<Self> {
        // Ensure the directory path exists.
        ensure!(directory.exists(), "The program directory does not exist: {}", directory.display());
        // Ensure the program name is valid.
        ensure!(!Program::is_reserved_keyword(id.name()), "Program name is invalid (reserved): {id}");

        // Construct the initial README string.
        let readme_string = format!(
            r"# {id}
## Build Guide
To compile this Aleo program, run:
```bash
aleo build
```
"
        );

        // Construct the file name.
        let file_name = "README.md".to_string();

        // Construct the file path.
        let path = directory.join(file_name);

        // Ensure the file path does not already exist.
        ensure!(!path.exists(), "README file already exists: {}", path.display());

        // Write the file.
        File::create(&path)?.write_all(readme_string.as_bytes())?;

        // Return the README file.
        Ok(Self { path })
    }

    /// Returns the file path.
    pub const fn path(&self) -> &PathBuf {
        &self.path
    }
}
