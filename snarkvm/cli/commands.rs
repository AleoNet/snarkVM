// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::cli::{Command, Updater};

pub fn parse(command: Command) -> anyhow::Result<String> {
    match command {
        Command::Update { list, quiet } => match list {
            true => match Updater::show_available_releases() {
                Ok(output) => Ok(output),
                Err(error) => Ok(format!("Failed to list the available versions of snarkVM\n{}\n", error)),
            },
            false => {
                let result = Updater::update_to_latest_release(!quiet);
                if !quiet {
                    match result {
                        Ok(status) => {
                            if status.uptodate() {
                                Ok("\nsnarkVM is already on the latest version".to_string())
                            } else if status.updated() {
                                Ok(format!("\nsnarkVM has updated to version {}", status.version()))
                            } else {
                                Ok("".to_string())
                            }
                        }
                        Err(e) => Ok(format!("\nFailed to update snarkVM to the latest version\n{}\n", e)),
                    }
                } else {
                    Ok("".to_string())
                }
            }
        }, // _ => Err(anyhow!("\nUnknown command\n")),
    }
}
