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

use std::{env, fs};
use std::path::PathBuf;
use clap::{Args, StructOpt};
use snarkvm::prelude::{Parser, Program};
use snarkvm_fuzz::harness::harness;

#[derive(Debug, Args)]
pub struct ExecuteCli {
    #[clap(parse(try_from_str), help = "Inputs to run", name = "INPUT")]
    input: Vec<PathBuf>,
}

impl ExecuteCli {
    pub fn run(self) {
        for path in self.input {
            let result = fs::read_to_string(path).unwrap();
            harness(result.as_bytes());
            println!("Execution finished");
        }
    }
}
