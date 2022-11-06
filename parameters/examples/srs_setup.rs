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

use anyhow::Result;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{
    fs,
    fs::File,
    io::{BufWriter, Read, Write},
    path::PathBuf,
};

fn sha256(data: &[u8]) -> [u8; 32] {
    let digest = Sha256::digest(data);
    let mut ret = [0u8; 32];
    ret.copy_from_slice(&digest);
    ret
}
fn checksum(bytes: &[u8]) -> String {
    hex::encode(sha256(bytes))
}

fn versioned_filename(filename: &str, checksum: &str) -> String {
    match checksum.get(0..7) {
        Some(sum) => format!("{}.{}", filename, sum),
        _ => filename.to_string(),
    }
}

/// Writes the given bytes to the given versioned filename.
fn write_remote(filename: &str, version: &str, bytes: &[u8]) -> Result<()> {
    let mut file = BufWriter::new(File::create(PathBuf::from(&versioned_filename(filename, version)))?);
    file.write_all(bytes)?;
    Ok(())
}

// /// Writes the given bytes to the given filename.
// fn write_local(filename: &str, bytes: &[u8]) -> Result<()> {
//     let mut file = BufWriter::new(File::create(PathBuf::from(filename))?);
//     file.write_all(bytes)?;
//     Ok(())
// }

/// Writes the given metadata as JSON to the given filename.
fn write_metadata(filename: &str, metadata: &Value) -> Result<()> {
    let mut file = BufWriter::new(File::create(PathBuf::from(filename))?);
    file.write_all(&serde_json::to_vec_pretty(metadata)?)?;
    Ok(())
}

pub fn usrs() -> Result<()> {
    let paths = fs::read_dir("../src/testnet3/resources/").unwrap();
    for path in paths {
        let path = path?.path();
        if let Some("usrs") = path.extension().and_then(|s| s.to_str()) {
            let metadata_path = path.with_extension("metadata");
            let mut file = File::open(&path)?;
            let file_size = file.metadata().unwrap().len() as usize;
            let mut file_bytes = Vec::with_capacity(file_size);
            file.read_to_end(&mut file_bytes)?;
            let checksum = checksum(&file_bytes);

            let metadata = json!({
                "checksum": checksum,
                "size": file_size,
            });

            write_metadata(metadata_path.to_str().unwrap(), &metadata)?;
            write_remote(path.to_str().unwrap(), &checksum, &file_bytes)?;
        }
    }

    Ok(())
}

/// Run the following command to perform a setup.
/// `cargo run --example setup [parameter] [network]`
pub fn main() -> Result<()> {
    usrs()
}
