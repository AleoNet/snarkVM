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

use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{bail, Result};
use std::path::{Path, PathBuf};

pub struct ObjectStore {
    root: PathBuf,
    keys: Vec<PathBuf>,
}

impl ObjectStore {
    pub fn new(root: PathBuf) -> Result<Self> {
        // Create the root directory if it does not exist.
        if !root.try_exists()? {
            std::fs::create_dir_all(&root)?;
        }
        Ok(Self { root, keys: Vec::new() })
    }

    pub fn keys(&self) -> impl Iterator<Item = &PathBuf> {
        self.keys.iter()
    }

    pub fn get<O: FromBytes, P: AsRef<Path>>(&mut self, path: P) -> Result<O> {
        let full_path = self.root.join(path);
        let bytes = std::fs::read(&full_path)?;
        O::from_bytes_le(&bytes)
    }

    pub fn insert<O: ToBytes, P: AsRef<Path>>(&mut self, path: P, object: &O) -> Result<()> {
        let full_path = self.root.join(path);
        let bytes = object.to_bytes_le()?;
        std::fs::write(&full_path, &bytes)?;
        self.keys.push(full_path);
        Ok(())
    }

    fn clear(&mut self) -> Result<()> {
        for key in self.keys() {
            std::fs::remove_file(key)?;
        }
        self.keys.clear();
        Ok(())
    }
}
