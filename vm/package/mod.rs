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

mod build;
mod clean;
mod is_build_required;
mod run;

use crate::{
    file::{AVMFile, AleoFile, Manifest, ProverFile, VerifierFile, README},
    prelude::{Identifier, Locator, Network, PrivateKey, ProgramID, Response, ToBytes, Value},
};
use snarkvm_compiler::{Execution, Process, Program};

use anyhow::{bail, ensure, Error, Result};
use colored::Colorize;
use core::str::FromStr;
use rand::{CryptoRng, Rng};
use std::path::{Path, PathBuf};

pub struct Package<N: Network> {
    /// The program ID.
    program_id: ProgramID<N>,
    /// The directory path.
    directory: PathBuf,
    /// The manifest file.
    manifest_file: Manifest<N>,
    /// The program file.
    program_file: AleoFile<N>,
}

impl<N: Network> Package<N> {
    /// Creates a new package, at the given directory with the given program name.
    pub fn create(directory: &Path, program_id: &ProgramID<N>) -> Result<Self> {
        // Ensure the directory path does not exist.
        ensure!(!directory.exists(), "The program directory already exists: {}", directory.display());
        // Ensure the program name is valid.
        ensure!(!Program::is_reserved_keyword(program_id.name()), "Program name is invalid (reserved): {program_id}");

        // Create the program directory.
        if !directory.exists() {
            std::fs::create_dir_all(directory)?;
        }

        // Create the manifest file.
        let manifest_file = Manifest::create(directory, program_id)?;
        // Create the program file.
        let program_file = AleoFile::create(directory, program_id, true)?;
        // Create the README file.
        let _readme_file = README::create::<N>(directory, program_id)?;

        Ok(Self { program_id: *program_id, directory: directory.to_path_buf(), manifest_file, program_file })
    }

    /// Opens the package at the given directory with the given program name.
    pub fn open(directory: &Path) -> Result<Self> {
        // Ensure the directory path exists.
        ensure!(directory.exists(), "The program directory does not exist: {}", directory.display());
        // Ensure the manifest file exists.
        ensure!(
            Manifest::<N>::exists_at(directory),
            "Missing '{}' at '{}'",
            Manifest::<N>::file_name(),
            directory.display()
        );
        // Ensure the main program file exists.
        ensure!(
            AleoFile::<N>::main_exists_at(directory),
            "Missing '{}' at '{}'",
            AleoFile::<N>::main_file_name(),
            directory.display()
        );

        // Create the manifest file.
        let manifest_file = Manifest::open(directory)?;
        // Retrieve the program ID.
        let program_id = *manifest_file.program_id();
        // Ensure the program name is valid.
        ensure!(!Program::is_reserved_keyword(program_id.name()), "Program name is invalid (reserved): {program_id}");

        // Create the program file.
        let program_file = AleoFile::open(directory, &program_id, true)?;

        Ok(Self { program_id, directory: directory.to_path_buf(), manifest_file, program_file })
    }

    /// Returns the program ID.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }

    /// Returns the directory path.
    pub const fn directory(&self) -> &PathBuf {
        &self.directory
    }

    /// Returns the manifest file.
    pub const fn manifest_file(&self) -> &Manifest<N> {
        &self.manifest_file
    }

    /// Returns the program file.
    pub const fn program_file(&self) -> &AleoFile<N> {
        &self.program_file
    }

    /// Returns the program.
    pub const fn program(&self) -> &Program<N> {
        self.program_file.program()
    }

    /// Returns the build directory.
    pub fn build_directory(&self) -> PathBuf {
        self.directory.join("build")
    }

    /// Returns a new process for the package.
    pub fn get_process<A: crate::circuit::Aleo<Network = N, BaseField = N::Field>>(&self) -> Result<Process<N, A>> {
        // Prepare the build directory.
        let build_directory = self.build_directory();
        // Ensure the build directory exists.
        if !build_directory.exists() {
            bail!("Build directory does not exist: {}", build_directory.display());
        }

        // Create the process.
        let mut process = Process::<N, A>::new(self.program().clone())?;

        // Prepare the imports directory.
        let mut imports_directory = build_directory;
        imports_directory.push("imports");

        // Add all import programs (in order) to the process.
        self.program().imports().keys().try_for_each(|program_id| {
            // Open the Aleo program file.
            let import_program_file = AleoFile::open(&imports_directory, program_id, false)?;
            // Add the import program.
            process.add_program(import_program_file.program())?;
            Ok::<_, Error>(())
        })?;

        Ok(process)
    }
}
