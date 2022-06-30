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

use clap::Parser;

#[derive(Debug, Parser)]
#[clap(name = "snarkVM", author = "The Aleo Team <hello@aleo.org>")]
pub struct CLI {
    /// Enable debug mode
    #[clap(short, long)]
    pub debug: bool,

    /// Enable verbose mode
    #[clap(short, long, parse(from_occurrences))]
    pub verbose: u8,

    #[clap(subcommand)]
    pub command: Command,
}

#[derive(Debug, Parser)]
pub enum Command {
    /// Update snarkVM to the latest version
    Update {
        /// Lists all available versions of snarkVM
        #[clap(short = 'l', long)]
        list: bool,

        /// Suppress outputs to terminal
        #[clap(short = 'q', long)]
        quiet: bool,
    },
}
