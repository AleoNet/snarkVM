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

use crate::{
    file::AleoFile,
    prelude::{Network, ProgramID},
};
use snarkvm_compiler::Program;

use anyhow::{ensure, Result};
use std::path::{Path, PathBuf};

pub struct Package<N: Network> {
    /// The program ID.
    id: ProgramID<N>,
    /// The directory path.
    directory: PathBuf,
    /// The program file.
    program_file: AleoFile<N>,
}

impl<N: Network> Package<N> {
    /// Creates a new package, at the given directory with the given program name.
    pub fn new(directory: &Path, id: &ProgramID<N>) -> Result<Self> {
        // Ensure the directory path does not exist.
        ensure!(!directory.exists(), "The program directory already exists: {}", directory.display());
        // Ensure the program name is valid.
        ensure!(!Program::is_reserved_keyword(id.name()), "Program name is invalid (reserved): {id}");

        // Create the program directory.
        std::fs::create_dir_all(directory)?;

        // Create the program file.
        let program_file = AleoFile::new(directory, id)?;

        Ok(Self { id: *id, directory: directory.to_path_buf(), program_file })
    }
}
