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
    file::Manifest,
    prelude::{FromBytes, Network, ProgramID, ToBytes},
};
use snarkvm_compiler::Program;

use anyhow::{anyhow, bail, ensure, Result};
use std::{
    fs::{self, File},
    io::Write,
    path::Path,
};

static AVM_FILE_EXTENSION: &str = "avm";

pub struct AVMFile<N: Network> {
    /// The file name (without the extension).
    file_name: String,
    /// The program.
    program: Program<N>,
}

impl<N: Network> AVMFile<N> {
    /// Creates a new AVM program file, given the directory path, program ID, and `is_main` indicator.
    pub fn create(directory: &Path, program: Program<N>, is_main: bool) -> Result<Self> {
        // Ensure the directory path exists.
        ensure!(directory.exists(), "The program directory does not exist: '{}'", directory.display());
        // Ensure the program name is valid.
        ensure!(
            !Program::is_reserved_keyword(program.id().name()),
            "Program name is invalid (reserved): {}",
            program.id()
        );

        // Create the file.
        let file_name = if is_main { Self::main_file_name() } else { format!("{}.{AVM_FILE_EXTENSION}", program.id()) };
        // Construct the file path.
        let path = directory.join(file_name);
        // Write the file (overwriting if it already exists).
        File::create(&path)?.write_all(&program.to_bytes_le()?)?;

        Self::from_filepath(&path)
    }

    /// Opens the AVM program file, given the directory path, program ID, and `is_main` indicator.
    pub fn open(directory: &Path, program_id: &ProgramID<N>, is_main: bool) -> Result<Self> {
        // Ensure the directory path exists.
        ensure!(directory.exists(), "The program directory does not exist: '{}'", directory.display());

        // Create the file.
        let file_name = if is_main { Self::main_file_name() } else { format!("{program_id}.{AVM_FILE_EXTENSION}") };
        // Construct the file path.
        let path = directory.join(file_name);
        // Ensure the file path exists.
        ensure!(path.exists(), "The AVM file is missing: '{}'", path.display());

        // Load the AVM file.
        let avm_file = Self::from_filepath(&path)?;

        // Ensure the program ID matches, if this is the main file.
        if is_main && avm_file.program.id() != program_id {
            bail!("The program ID from `{}` does not match in '{}'", Manifest::<N>::file_name(), path.display())
        }

        Ok(avm_file)
    }

    /// Returns `true` if the file exists at the given path.
    pub fn exists_at(&self, file_path: &Path) -> bool {
        // Ensure the path is well-formed.
        Self::check_path(file_path).is_ok() && file_path.exists()
    }

    /// Returns `true` if the main program file exists at the given directory path.
    pub fn main_exists_at(directory: &Path) -> bool {
        // Construct the file path.
        let path = directory.join(Self::main_file_name());
        // Return the result.
        path.is_file() && path.exists()
    }

    /// Returns the main AVM program file name.
    pub fn main_file_name() -> String {
        format!("main.{AVM_FILE_EXTENSION}")
    }

    /// Returns the file name.
    pub fn file_name(&self) -> &str {
        &self.file_name
    }

    /// Returns the program.
    pub const fn program(&self) -> &Program<N> {
        &self.program
    }

    /// Removes the file at the given path, if it exists.
    pub fn remove(&self, path: &Path) -> Result<()> {
        // If the path does not exist, do nothing.
        if !path.exists() {
            Ok(())
        } else {
            // Ensure the path is well-formed.
            Self::check_path(path)?;
            // If the path exists, remove it.
            if path.exists() {
                // Remove the file.
                fs::remove_file(&path)?;
            }
            Ok(())
        }
    }
}

impl<N: Network> AVMFile<N> {
    /// Checks that the given path has the correct file extension.
    fn check_path(path: &Path) -> Result<()> {
        // Ensure the given path is a file.
        ensure!(path.is_file(), "The path is not a file.");

        // Ensure the given path has the correct file extension.
        let extension = path.extension().ok_or_else(|| anyhow!("File extension not found."))?;
        ensure!(extension == AVM_FILE_EXTENSION, "File extension is incorrect.");

        Ok(())
    }

    /// Reads the AVM program from the given file path, if it exists.
    fn from_filepath(file: &Path) -> Result<Self> {
        // Ensure the path is well-formed.
        Self::check_path(file)?;

        // Ensure the given path exists.
        ensure!(file.exists(), "File does not exist: {}", file.display());

        // Retrieve the file name.
        let file_name = file
            .file_stem()
            .ok_or_else(|| anyhow!("File name not found."))?
            .to_str()
            .ok_or_else(|| anyhow!("File name not found."))?
            .to_string();

        // Read the program bytes.
        let program_bytes = fs::read(&file)?;
        // Parse the program bytes.
        let program = Program::from_bytes_le(&program_bytes)?;

        Ok(Self { file_name, program })
    }

    /// Writes the AVM program to the file.
    pub fn write_to(&self, path: &Path) -> Result<()> {
        // Ensure the path is well-formed.
        Self::check_path(path)?;

        // Retrieve the file name.
        let file_name = path
            .file_stem()
            .ok_or_else(|| anyhow!("File name not found."))?
            .to_str()
            .ok_or_else(|| anyhow!("File name not found."))?
            .to_string();
        // Ensure the file name matches the expected file name.
        ensure!(file_name == self.file_name, "File name does not match.");

        Ok(File::create(&path)?.write_all(&self.program.to_bytes_le()?)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::Parser;

    type CurrentNetwork = snarkvm_console::network::Testnet3;

    fn temp_dir() -> std::path::PathBuf {
        tempfile::tempdir().expect("Failed to open temporary directory").into_path()
    }

    #[test]
    fn test_from_path() {
        // Initialize a temporary directory.
        let directory = temp_dir();

        let program_string = r"
program token.aleo;

record token:
    owner as address.private;
    balance as u64.private;
    token_amount as u64.private;

function compute:
    input r0 as token.record;
    add r0.token_amount r0.token_amount into r1;
    output r1 as u64.private;";

        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(program_string).unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Write the program bytes to a file in the temporary directory.
        let path = directory.join("token.avm");
        let mut file = File::create(&path).unwrap();
        file.write_all(&program.to_bytes_le().unwrap()).unwrap();

        // Read the program from the path.
        let file = AVMFile::from_filepath(&path).unwrap();

        assert_eq!("token", file.file_name());
        assert_eq!(&program, file.program());
    }
}
