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

extern crate cc;

use std::{env, path::PathBuf};

#[cfg(feature = "blstasm")]
fn compile_blst_asm() {
    let mut file_vec = Vec::new();

    let blst_base_dir = match env::var("BLST_SRC_DIR") {
        Ok(val) => PathBuf::from(val),
        Err(_) => PathBuf::from("src/msm/variable_base/blst_377_asm"),
    };
    println!("Using blst source directory {}", blst_base_dir.display());

    file_vec.push(blst_base_dir.join("blst_377_ops.cpp"));
    file_vec.push(blst_base_dir.join("sn_msm.cpp"));
    file_vec.push(blst_base_dir.join("build/assembly.S"));
    // file_vec.push(blst_base_dir.join("asm.cpp"));

    // Set CC environment variable to choose alternative C compiler.
    // Optimization level depends on whether or not --release is passed
    // or implied.
    let mut cc = cc::Build::new();

    // account for cross-compilation
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    if target_arch != "x86_64" {
        panic!("invalid arch for asm, expected x86_64");
    }

    //todo: cpuid
    cc.define("__ADX__", None);

    // cc.flag_if_supported("-mno-avx"); // avoid costly transitions
    cc.flag_if_supported("-march=native");
    if !cfg!(debug_assertions) {
        cc.opt_level(2);
    }
    cc.files(&file_vec).cpp(true).compile("libblst377.a");
}

#[cfg(not(feature = "blstasm"))]
fn compile_blst_asm() {}

fn main() {
    compile_blst_asm();
}
