// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    prelude::{Network, ProgramID},
    synthesizer::Program,
};

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
}

impl<N: Network> Manifest<N> {
/// Creates a new manifest file with the given directory path and program ID.
    pub fn create(directory: &Path, id: &ProgramID<N>) -> Result<Self> {
// Ensure the directory path exists.
        ensure!(directory.exists(), "The program directory does not exist: '{}'", directory.display());
// Ensure the program name is valid.
        ensure!(!Program::is_reserved_keyword(id.name()), "Program name is invalid (reserved): {id}");

        // Construct the initial program manifest string.
        let manifest_string = format!(
            r#"{{
    "program": "{id}",
    "version": "0.0.0",
    "description": "",
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
        Ok(Self { path, program_id: *id })
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
        // Deserialize the JSON string into the manifest structure.
        let manifest: Manifest<N> = serde_json::from_str(&manifest_string)?;

        ensure!(!Program::is_reserved_keyword(manifest.program_id.name()), "Program name is invalid (reserved): {manifest.program_id}");

        Ok(manifest)
    }

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
}

// Implement serde serialization and deserialization for Manifest structure.
impl<N: Network> serde::Serialize for Manifest<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("Manifest", 2)?;
        state.serialize_field("program", &self.program_id.to_string())?;
        state.serialize_field("version", "0.0.0")?;
        state.serialize_field("description", "")?;
        state.serialize_field("license", "MIT")?;
        state.end()
    }
}

impl<'de, N: Network> serde::Deserialize<'de> for Manifest<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(serde::Deserialize)]
        struct ManifestData {
            program: String,
            // Other fields if needed in the future.
        }

        let manifest_data = ManifestData::deserialize(deserializer)?;
        let program_id = ProgramID::from_str(&manifest_data.program)
            .map_err(|e| serde::de::Error::custom(format!("Failed to parse program ID: {}", e)))?;

        Ok(Manifest {
            path: Default::default(),
            program_id,
        })
    }
}
