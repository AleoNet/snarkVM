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

use std::env;
use std::path::PathBuf;

fn main() {
    /*
     * Use pre-built libblst.a if there is one. This is primarily
     * for trouble-shooting purposes. Idea is that libblst.a can be
     * compiled with flags independent from cargo defaults, e.g.
     * '../../build.sh -O1 ...'.
     */
    // if Path::new("libblst377.a").exists() {
    //     println!("cargo:rustc-link-search=.");
    //     println!("cargo:rustc-link-lib=blst");
    //     return;
    // }

    let mut file_vec = Vec::new();

    let blst_base_dir = match env::var("BLST_SRC_DIR") {
        Ok(val) => PathBuf::from(val),
        Err(_) => PathBuf::from("src/msm/blst_377"),
    };
    println!("Using blst source directory {}", blst_base_dir.display());

    file_vec.push(blst_base_dir.join("blst_377_ops.cpp"));
    file_vec.push(blst_base_dir.join("sn_msm.cpp"));
    //
    file_vec.push(blst_base_dir.join("build/assembly.S"));
    // file_vec.push(blst_base_dir.join("asm.cpp"));

    // Set CC environment variable to choose alternative C compiler.
    // Optimization level depends on whether or not --release is passed
    // or implied.
    let mut cc = cc::Build::new();

    // account for cross-compilation
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    match (cfg!(feature = "portable"), cfg!(feature = "force-adx")) {
        (true, false) => {
            println!("Compiling in portable mode without ISA extensions");
            cc.define("__BLST_PORTABLE__", None);
        }
        (false, true) => {
            if target_arch.eq("x86_64") {
                println!("Enabling ADX support via `force-adx` feature");
                cc.define("__ADX__", None);
            } else {
                println!("`force-adx` is ignored for non-x86_64 targets");
            }
        }
        (false, false) => {
            #[cfg(target_arch = "x86_64")]
            if target_arch.eq("x86_64") && cfg!(target_feature = "adx")
            {
                println!("Enabling ADX because it was detected on the host");
                cc.define("__ADX__", None);
            }
        }
        (true, true) => panic!(
            "Cannot compile with both `portable` and `force-adx` features"
        ),
    }
    // cc.flag_if_supported("-mno-avx"); // avoid costly transitions
    cc.flag_if_supported("-march=native");
    if !cfg!(debug_assertions) {
        cc.opt_level(2);
    }
    cc.files(&file_vec).cpp(true).compile("libblst377.a");
}
