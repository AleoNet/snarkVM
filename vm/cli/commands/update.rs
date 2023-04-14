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
use crate::cli::helpers::Updater;

/// Update SnarkVM to the latest version
#[derive(Debug, Parser)]
pub struct Update {
    /// Lists all available versions of Aleo
    #[clap(short = 'l', long)]
    list: bool,
    /// Suppress outputs to terminal
    #[clap(short = 'q', long)]
    quiet: bool,
}

impl Update {
    pub fn parse(self) -> Result<String> {
        match self.list {
            true => match Updater::show_available_releases() {
                Ok(output) => Ok(output),
                Err(error) => Ok(format!("Failed to list the available versions of Aleo\n{error}\n")),
            },
            false => {
                let result = Updater::update_to_latest_release(!self.quiet);
                if !self.quiet {
                    match result {
                        Ok(status) => {
                            if status.uptodate() {
                                Ok("\nAleo is already on the latest version".to_string())
                            } else if status.updated() {
                                Ok(format!("\nAleo has updated to version {}", status.version()))
                            } else {
                                Ok(String::new())
                            }
                        }
                        Err(e) => Ok(format!("\nFailed to update Aleo to the latest version\n{e}\n")),
                    }
                } else {
                    Ok(String::new())
                }
            }
        }
    }
}
