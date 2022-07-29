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

use snarkvm_algorithms::{
    crypto_hash::sha256::sha256,
    snark::marlin::{ahp::AHPForR1CS, MarlinHidingMode},
    SNARK,
};

use anyhow::Result;
use serde_json::{json, Value};
use std::{
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

pub fn kzg_powers_metadata() {
    for i in 16..=28 {
        let degree_file_name = format!("powers_of_g_{}", i);
        let degree_metadata = format!("powers_of_g_{}_metadata", i);
        let mut degree_file = File::open(degree_file_name).unwrap();
        let degree_file_size = degree_file.metadata().unwrap().len() as usize;
        let mut degree_file_bytes = Vec::with_capacity(degree_file_size);
        degree_file.read_to_end(&mut degree_file_bytes).unwrap();
        let checksum = checksum(&degree_file_bytes);

        let metadata = json!({
            "degree": i as usize,
            "checksum": checksum,
            "size": degree_file_size,
        });

        write_metadata(&degree_metadata, &metadata).unwrap();
    }
}

/// Runs the trial SRS setup. (cargo run --release --example setup trial_srs 524288)
pub fn trial_srs<N: snarkvm_console::network::Network>(num_gates: usize) -> Result<()> {
    const TRIAL_SRS_METADATA: &str = "universal.srs.trial.metadata";
    const TRIAL_SRS: &str = "universal.srs.trial";

    let mut rng = snarkvm_utilities::test_crypto_rng_fixed();

    use snarkvm_algorithms::{crypto_hash::PoseidonSponge, snark::marlin};
    use snarkvm_console::network::Environment;
    use snarkvm_curves::PairingEngine;
    use snarkvm_utilities::{CanonicalSerialize, Compress};

    type Fq<N> = <<N as Environment>::PairingCurve as PairingEngine>::Fq;
    type Fr<N> = <N as Environment>::Field;
    type FS<N> = marlin::fiat_shamir::FiatShamirAlgebraicSpongeRng<Fr<N>, Fq<N>, PoseidonSponge<Fq<N>, 6, 1>>;
    type Marlin<N> = marlin::MarlinSNARK<<N as Environment>::PairingCurve, FS<N>, MarlinHidingMode, [Fr<N>]>;

    let timer = std::time::Instant::now();
    let max_degree = AHPForR1CS::<N::Field, MarlinHidingMode>::max_degree(num_gates, num_gates, num_gates).unwrap();
    let universal_srs = Marlin::<N>::universal_setup(&max_degree, &mut rng)?;
    println!("Called universal setup: {} ms", timer.elapsed().as_millis());

    let mut srs_bytes = vec![];
    universal_srs.serialize_with_mode(&mut srs_bytes, Compress::No)?;

    let srs_checksum = checksum(&srs_bytes);

    let srs_metadata = json!({
        "checksum": srs_checksum,
        "size": srs_bytes.len(),
    });

    println!("{}", serde_json::to_string_pretty(&srs_metadata)?);
    write_metadata(TRIAL_SRS_METADATA, &srs_metadata)?;
    write_remote(TRIAL_SRS, &srs_checksum, &srs_bytes)?;

    Ok(())
}

/// Run the following command to perform a setup.
/// `cargo run --example setup [parameter] [network]`
pub fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("Invalid number of arguments. Given: {} - Required: 2", args.len() - 1);
        return Ok(());
    }

    match args[1].as_str() {
        "trial_srs" => trial_srs::<snarkvm_console::network::Testnet3>(args[2].as_str().parse::<usize>()?)?,
        _ => panic!("Invalid parameter"),
    };

    Ok(())
}
