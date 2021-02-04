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

use structopt::StructOpt;

#[derive(StructOpt, Debug)]
#[structopt(name = "snarkVM", author = "The Aleo Team <hello@aleo.org>", setting = structopt::clap::AppSettings::ColoredHelp)]
pub struct CLI {
    /// Enable debug mode
    #[structopt(short, long)]
    pub debug: bool,

    /// Enable verbose mode
    #[structopt(short, long, parse(from_occurrences))]
    pub verbose: u8,

    #[structopt(subcommand)]
    pub command: Command,
}

#[derive(StructOpt, Debug)]
pub enum Command {
    // /// Generates a new Aleo account
// New {
//     /// Seed the RNG with a numeric value
//     #[structopt(short = "s", long)]
//     seed: Option<u64>,
// },
// /// Update Aleo to the latest version
// Update {
//     /// Lists all available versions of Aleo
//     #[structopt(short = "l", long)]
//     list: bool,
//
//     /// Suppress outputs to terminal
//     #[structopt(short = "q", long)]
//     quiet: bool,
// },
}
