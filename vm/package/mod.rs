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

pub use build::{BuildRequest, BuildResponse};

use crate::{
    file::{AVMFile, AleoFile, Manifest, ProverFile, VerifierFile, README},
    prelude::{
        de,
        Deserialize,
        Deserializer,
        Identifier,
        Locator,
        Network,
        PrivateKey,
        ProgramID,
        Response,
        Serialize,
        SerializeStruct,
        Serializer,
        Value,
    },
};
use snarkvm_compiler::{CallOperator, Execution, Instruction, Process, Program, ProvingKey, VerifyingKey};

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

        // Open the manifest file.
        let manifest_file = Manifest::open(directory)?;
        // Retrieve the program ID.
        let program_id = *manifest_file.program_id();
        // Ensure the program name is valid.
        ensure!(!Program::is_reserved_keyword(program_id.name()), "Program name is invalid (reserved): {program_id}");

        // Open the program file.
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

    /// Returns the imports directory.
    pub fn imports_directory(&self) -> PathBuf {
        self.directory.join("imports")
    }

    /// Returns a new process for the package.
    pub fn get_process(&self) -> Result<Process<N>> {
        // Prepare the build directory.
        let build_directory = self.build_directory();
        // Ensure the build directory exists.
        if !build_directory.exists() {
            bail!("Build directory does not exist: {}", build_directory.display());
        }

        // Create the process.
        let mut process = Process::<N>::new()?;

        // Prepare the imports directory.
        let imports_directory = self.imports_directory();

        // Add all import programs (in order) to the process.
        self.program().imports().keys().try_for_each(|program_id| {
            // Open the Aleo program file.
            let import_program_file = AleoFile::open(&imports_directory, program_id, false)?;
            // Add the import program.
            process.add_program(import_program_file.program())?;
            Ok::<_, Error>(())
        })?;

        // Add the program to the process.
        process.add_program(self.program())?;

        Ok(process)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console::network::Testnet3;
    use std::{fs::File, io::Write};

    type CurrentNetwork = Testnet3;

    fn temp_dir() -> PathBuf {
        tempfile::tempdir().expect("Failed to open temporary directory").into_path()
    }

    #[test]
    fn test_get_process() {
        // Initialize a temporary directory.
        let directory = temp_dir();

        let program_id = ProgramID::<CurrentNetwork>::from_str("token.aleo").unwrap();

        let program_string = r"
program token.aleo;

record token:
    owner as address.private;
    gates as u64.private;
    token_amount as u64.private;

function compute:
    input r0 as token.record;
    add.w r0.token_amount r0.token_amount into r1;
    output r1 as u64.private;";

        // Write the program string to a file in the temporary directory.
        let path = directory.join("main.aleo");
        let mut file = File::create(&path).unwrap();
        file.write_all(program_string.as_bytes()).unwrap();

        // Create the manifest file.
        let _manifest_file = Manifest::create(&directory, &program_id).unwrap();

        // Create the build directory.
        let build_directory = directory.join("build");
        std::fs::create_dir_all(&build_directory).unwrap();

        // Open the package at the temporary directory.
        let package = Package::<Testnet3>::open(&directory).unwrap();

        // Get the program process and check all instructions.
        assert!(package.get_process().is_ok());
        assert_eq!(package.program_id(), &program_id);
    }
}
