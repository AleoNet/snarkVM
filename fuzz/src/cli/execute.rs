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
use std::os::raw::c_int;
use std::path::PathBuf;
use clap::{Args, StructOpt};
use tokio::runtime::Builder;
use tokio::task::JoinHandle;
use snarkvm::prelude::{Parser, Program};
use snarkvm_fuzz::harness::harness;

#[derive(Debug, Args)]
pub struct ExecuteCli {
    #[clap(parse(try_from_str), help = "Inputs to run", name = "INPUT")]
    input: Vec<PathBuf>,
}

#[cfg(feature = "coverage")]
extern "C" {
    fn __llvm_profile_write_file() -> c_int;
}

impl ExecuteCli {
    pub fn run(self) {
        let inputs = self.input;
        Builder::new_multi_thread()
            .thread_name("execute")
            .build()
            .unwrap()
            .block_on(async move {
                let handles: Vec<JoinHandle<()>> = inputs.iter().cloned().map(|path| tokio::spawn(async {
                    println!("Executing {:?}", &path);
                    if let Ok(string) = fs::read_to_string(path) {
                        harness(string.as_bytes());
                        println!("Execution finished");
                    }
                })).collect::<Vec<_>>();

                for handle in handles {
                    handle.await.unwrap();
                }
            });
    }
}
