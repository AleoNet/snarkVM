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
use clap::StructOpt;
use snarkvm::prelude::{Parser, Program};
use snarkvm_fuzz::harness::FuzzNetwork;

#[derive(Debug, StructOpt)]
pub struct SeedCli {

}

impl SeedCli {
    pub fn run(self) {
        let current_dir = env::current_dir().unwrap();


        for entry in fs::read_dir(current_dir.join("afl/seeds")).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();

            if path.is_file() {
                let result = fs::read_to_string(path).unwrap();
                let program = Program::<FuzzNetwork>::parse(&result).unwrap();

            }


        }
    }
}
