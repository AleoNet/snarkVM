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

use snarkvm_algorithms::crypto_hash::sha256::sha256;
use snarkvm_circuit::Aleo;
use snarkvm_console::network::{Network, Testnet3};
use snarkvm_synthesizer::{Process, Program};

use anyhow::Result;
use serde_json::{json, Value};
use snarkvm_utilities::ToBytes;
use std::{
    fs,
    fs::File,
    io::{BufWriter, Read, Write},
    path::PathBuf,
};

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

/// (Do not use) Writes the metadata files. (cargo run --release --example setup usrs)
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

/// Synthesizes the circuit keys for the credits program. (cargo run --release --example setup credits)
pub fn credits_program<N: Network, A: Aleo<Network = N>>() -> Result<()> {
    // Initialize an RNG.
    let rng = &mut snarkvm_utilities::TestRng::fixed(1245897092);
    // Initialize the process.
    let process = Process::setup::<A, _>(rng)?;
    // Initialize the program.
    let program = Program::<N>::credits()?;
    let program_id = program.id();

    // Initialize a vector for the commands.
    let mut commands = vec![];

    // Store the 'credits.aleo' circuit keys.
    for (function_name, _) in program.functions().iter() {
        // let timer = std::time::Instant::now();
        // process.synthesize_key::<A, _>(program_id, function_name, rng)?;
        // println!("Synthesized '{}': {} ms", function_name, timer.elapsed().as_millis());

        let proving_key = process.get_proving_key(program_id, function_name)?;
        let proving_key_bytes = proving_key.to_bytes_le()?;
        let proving_key_checksum = checksum(&proving_key_bytes);

        let verifying_key = process.get_verifying_key(program_id, function_name)?;
        let verifying_key_bytes = verifying_key.to_bytes_le()?;
        let verifying_key_checksum = checksum(&verifying_key_bytes);

        let metadata = json!({
            "prover_checksum": proving_key_checksum,
            "prover_size": proving_key_bytes.len(),
            "verifier_checksum": verifying_key_checksum,
            "verifier_size": verifying_key_bytes.len(),
        });

        println!("{}", serde_json::to_string_pretty(&metadata)?);
        write_metadata(&format!("{function_name}.metadata"), &metadata)?;
        write_remote(&format!("{function_name}.prover"), &proving_key_checksum, &proving_key_bytes)?;
        write_remote(&format!("{function_name}.verifier"), &verifying_key_checksum, &verifying_key_bytes)?;

        commands.push(format!(
            "snarkup upload \"{}\"",
            versioned_filename(&format!("{function_name}.prover"), &proving_key_checksum)
        ));
        commands.push(format!(
            "snarkup upload \"{}\"",
            versioned_filename(&format!("{function_name}.verifier"), &verifying_key_checksum)
        ));
    }

    // Print the commands.
    println!("\nNow, run the following commands:\n");
    println!("snarkup remove provers");
    println!("snarkup remove verifiers\n");
    for command in commands {
        println!("{command}");
    }
    println!();

    Ok(())
}

/// Run the following command to perform a setup.
/// `cargo run --example setup [variant]`
pub fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("Invalid number of arguments. Given: {} - Required: 2", args.len() - 1);
        return Ok(());
    }

    match args[1].as_str() {
        "usrs" => usrs()?,
        "credits" => credits_program::<Testnet3, snarkvm_circuit::AleoV0>()?,
        _ => panic!("Invalid parameter"),
    };

    Ok(())
}
