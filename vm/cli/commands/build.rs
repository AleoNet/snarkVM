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

/// Compiles an Aleo program.
#[derive(Debug, Parser)]
pub struct Build {
    /// Uses the specified endpoint.
    #[clap(long)]
    endpoint: Option<String>,
    /// Toggles offline mode.
    #[clap(long)]
    offline: bool,
}

impl Build {
    /// Compiles an Aleo program with the specified name.
    pub fn parse(self) -> Result<String> {
        // Derive the program directory path.
        let path = std::env::current_dir()?;

        // Load the package.
        let package = Package::open(&path)?;

        // Build the package, if the package requires building.
        package.build::<Aleo>(self.endpoint)?;

        // package.build::<Aleo>(match self.offline {
        //     true => None,
        //     false => Some(endpoint.unwrap_or("https://vm.aleo.org/testnet3/build".to_string())),
        // })?;

        // Prepare the path string.
        let path_string = format!("(in \"{}\")", path.display());

        // Log the build as successful.
        Ok(format!("✅ Built '{}' {}", package.program_id().to_string().bold(), path_string.dimmed()))
    }
}
