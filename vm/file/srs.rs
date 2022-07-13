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

use crate::prelude::{FromBytes, Network, ToBytes};
use snarkvm_compiler::UniversalSRS;

use anyhow::{ensure, Result};
use std::{
    fs::File,
    io::Write,
    path::{Path, PathBuf},
};

const UNIVERSAL_SRS: &str = ".universal.srs";

pub struct SRSFile<N: Network> {
    /// The file path.
    path: PathBuf,
    /// The universal SRS.
    universal_srs: UniversalSRS<N>,
}

impl<N: Network> SRSFile<N> {
    /// Creates a new manifest file with the given directory path.
    pub fn create(directory: &Path) -> Result<Self> {
        // Ensure the directory path exists.
        ensure!(directory.exists(), "The build directory does not exist: '{}'", directory.display());

        // Construct the file path.
        let path = directory.join(UNIVERSAL_SRS);
        // Ensure the file path does not already exist.
        ensure!(!path.exists(), "SRS file already exists: '{}'", path.display());

        // Load the SRS.
        let universal_srs = UniversalSRS::load(100_000)?;

        // Write the file.
        File::create(&path)?.write_all(&universal_srs.to_bytes_le()?)?;

        // Return the SRS file.
        Ok(Self { path, universal_srs })
    }

    /// Opens the SRS file for reading.
    pub fn open(directory: &Path) -> Result<Self> {
        // Ensure the directory path exists.
        ensure!(directory.exists(), "The build directory does not exist: '{}'", directory.display());

        // Construct the file path.
        let path = directory.join(UNIVERSAL_SRS);
        // Ensure the file path exists.
        ensure!(path.exists(), "SRS file is missing: '{}'", path.display());

        // Read the file.
        let universal_srs = UniversalSRS::read_le(std::io::BufReader::new(File::open(&path)?))?;

        // Return the SRS file.
        Ok(Self { path, universal_srs })
    }

    /// Returns `true` if the SRS file exists at the given path.
    pub fn exists_at(directory: &Path) -> bool {
        // Construct the file path.
        let path = directory.join(UNIVERSAL_SRS);
        // Return the result.
        path.is_file() && path.exists()
    }

    /// Returns the universal SRS file name.
    pub const fn file_name() -> &'static str {
        UNIVERSAL_SRS
    }

    /// Returns the file path.
    pub const fn path(&self) -> &PathBuf {
        &self.path
    }

    /// Returns the universal SRS.
    pub fn universal_srs(self) -> UniversalSRS<N> {
        self.universal_srs
    }
}
