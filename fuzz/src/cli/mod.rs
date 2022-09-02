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

use fuzz::FuzzCli;
use execute::ExecuteCli;
use clap::{self, Parser, StructOpt, Subcommand};

mod execute;
mod fuzz;

#[derive(Parser)]
#[clap(
    name = "snarkVM fuzzer",
    about = "A fuzzer for snarkVM based on LibAFL",
)]
pub struct Cli {
    #[clap(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Execute(ExecuteCli),
    Fuzz(FuzzCli),
}


impl Cli {
    pub fn run(self) {
        match self.command {
            Commands::Fuzz(cli) => {
                cli.fuzz()
            }
            Commands::Execute(execute) => {
                execute.run();
            }
        }
    }
}
