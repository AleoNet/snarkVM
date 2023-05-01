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

use super::*;

/// Cleans the Aleo package build directory.
#[derive(Debug, Parser)]
pub struct Clean;

impl Clean {
    /// Cleans an Aleo package build directory.
    pub fn parse(self) -> Result<String> {
        // Derive the program directory path.
        let path = std::env::current_dir()?;

        // Clean the build directory.
        Package::<CurrentNetwork>::clean(&path)?;

        // Prepare the path string.
        let path_string = format!("(in \"{}\")", path.join("build").display());

        Ok(format!("✅ Cleaned the build directory {}", path_string.dimmed()))
    }
}
