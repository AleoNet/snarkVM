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

use crate::cli::commands::{Build, Clean, New, Run, Update};

use anyhow::Result;
use clap::Parser;

#[derive(Debug, Parser)]
#[clap(name = "snarkVM", author = "The Aleo Team <hello@aleo.org>", setting = clap::AppSettings::ColoredHelp)]
pub struct CLI {
    /// Specify the verbosity [options: 0, 1, 2, 3]
    #[clap(default_value = "2", short, long)]
    pub verbosity: u8,
    /// Specify a subcommand.
    #[clap(subcommand)]
    pub command: Command,
}

#[derive(Debug, Parser)]
pub enum Command {
    #[clap(name = "build")]
    Build(Build),
    #[clap(name = "clean")]
    Clean(Clean),
    #[clap(name = "new")]
    New(New),
    #[clap(name = "run")]
    Run(Run),
    #[clap(name = "update")]
    Update(Update),
}

impl Command {
    /// Parse the command.
    pub fn parse(self) -> Result<String> {
        match self {
            Self::Build(command) => command.parse(),
            Self::Clean(command) => command.parse(),
            Self::New(command) => command.parse(),
            Self::Run(command) => command.parse(),
            Self::Update(command) => command.parse(),
        }
    }
}
