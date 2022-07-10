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

use crate::prelude::{Address, Network, PrivateKey, ProgramID};
use snarkvm_compiler::Program;

use anyhow::{anyhow, ensure, Result};
use core::str::FromStr;
use std::{
    fs::{self, File},
    io::Write,
    path::{Path, PathBuf},
};

const MANIFEST_FILE_NAME: &str = "program.json";

pub struct Manifest<N: Network> {
    /// The file path.
    path: PathBuf,
    /// The program ID.
    program_id: ProgramID<N>,
    /// The development private key.
    development_private_key: PrivateKey<N>,
    /// The development address.
    development_address: Address<N>,
}

impl<N: Network> Manifest<N> {
    /// Creates a new manifest file with the given directory path and program ID.
    pub fn create(directory: &Path, id: &ProgramID<N>) -> Result<Self> {
        // Ensure the directory path exists.
        ensure!(directory.exists(), "The program directory does not exist: '{}'", directory.display());
        // Ensure the program name is valid.
        ensure!(!Program::is_reserved_keyword(id.name()), "Program name is invalid (reserved): {id}");

        // Initialize an RNG.
        let rng = &mut rand::thread_rng();

        // Initialize a new development private key.
        let private_key = PrivateKey::<N>::new(rng)?;
        let address = Address::try_from(&private_key)?;

        // Construct the initial program manifest string.
        let manifest_string = format!(
            r#"{{
    "program": "{id}",
    "version": "0.0.0",
    "description": "",
    "development": {{
        "private_key": "{private_key}",
        "address": "{address}"
    }},
    "license": "MIT"
}}
"#
        );

        // Construct the file path.
        let path = directory.join(MANIFEST_FILE_NAME);
        // Ensure the file path does not already exist.
        ensure!(!path.exists(), "Manifest file already exists: '{}'", path.display());

        // Write the file.
        File::create(&path)?.write_all(manifest_string.as_bytes())?;

        // Return the manifest file.
        Ok(Self { path, program_id: *id, development_private_key: private_key, development_address: address })
    }

    /// Opens the manifest file for reading.
    pub fn open(directory: &Path) -> Result<Self> {
        // Ensure the directory path exists.
        ensure!(directory.exists(), "The program directory does not exist: '{}'", directory.display());

        // Construct the file path.
        let path = directory.join(MANIFEST_FILE_NAME);
        // Ensure the file path exists.
        ensure!(path.exists(), "Manifest file is missing: '{}'", path.display());

        // Read the file to a string.
        let manifest_string = fs::read_to_string(&path)?;
        let json: serde_json::Value = serde_json::from_str(&manifest_string)?;

        // Retrieve the program ID.
        let id_string = json["program"].as_str().ok_or_else(|| anyhow!("Program ID not found."))?;
        let id = ProgramID::from_str(id_string)?;
        // Ensure the program name is valid.
        ensure!(!Program::is_reserved_keyword(id.name()), "Program name is invalid (reserved): {id}");

        // Retrieve the development private key.
        let development_private_key_string =
            json["development"]["private_key"].as_str().ok_or_else(|| anyhow!("Development private key not found."))?;
        let development_private_key = PrivateKey::from_str(development_private_key_string)?;

        // Retrieve the development address.
        let development_address_string =
            json["development"]["address"].as_str().ok_or_else(|| anyhow!("Development address not found."))?;
        let development_address = Address::from_str(development_address_string)?;
        // Ensure the development address matches the development private key.
        ensure!(
            development_address == Address::try_from(&development_private_key)?,
            "Development address does not match development private key."
        );

        // Return the manifest file.
        Ok(Self { path, program_id: id, development_private_key, development_address })
    }

    /// Returns `true` if the manifest file exists at the given path.
    pub fn exists_at(directory: &Path) -> bool {
        // Construct the file path.
        let path = directory.join(MANIFEST_FILE_NAME);
        // Return the result.
        path.is_file() && path.exists()
    }

    /// Returns the manifest file name.
    pub const fn file_name() -> &'static str {
        MANIFEST_FILE_NAME
    }

    /// Returns the file path.
    pub const fn path(&self) -> &PathBuf {
        &self.path
    }

    /// Returns the program ID.
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }

    /// Returns the development private key.
    pub const fn development_private_key(&self) -> &PrivateKey<N> {
        &self.development_private_key
    }

    /// Returns the development address.
    pub const fn development_address(&self) -> &Address<N> {
        &self.development_address
    }
}
