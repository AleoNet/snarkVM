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
    CRH,
    SNARK,
    SRS,
};
use snarkvm_dpc::{InputCircuit, Network, OutputCircuit, PoSWScheme};
use snarkvm_utilities::{FromBytes, ToBytes, ToMinimalBits};

use anyhow::Result;
use rand::{prelude::ThreadRng, thread_rng};
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

/// Writes the given bytes to the given filename.
fn write_local(filename: &str, bytes: &[u8]) -> Result<()> {
    let mut file = BufWriter::new(File::create(PathBuf::from(filename))?);
    file.write_all(bytes)?;
    Ok(())
}

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

/// Runs the input circuit setup.
pub fn input_setup<N: Network>() -> Result<()> {
    const INPUT_CIRCUIT_METADATA: &str = "input.metadata";
    const INPUT_PROVING_KEY: &str = "input.proving";
    const INPUT_VERIFYING_KEY: &str = "input.verifying";

    let (input_proving_key, input_verifying_key) =
        N::InputSNARK::setup(&InputCircuit::<N>::blank(), &mut SRS::CircuitSpecific(&mut thread_rng()))?;

    let input_circuit_id =
        hex::encode(N::input_circuit_id_crh().hash(&input_verifying_key.to_minimal_bits())?.to_bytes_le()?);
    let input_proving_key = input_proving_key.to_bytes_le()?;
    let input_proving_checksum = checksum(&input_proving_key);
    let input_verifying_key = input_verifying_key.to_bytes_le()?;

    let input_metadata = json!({
        "proving_checksum": input_proving_checksum,
        "proving_size": input_proving_key.len(),
        "verifying_checksum": checksum(&input_verifying_key),
        "verifying_size": input_verifying_key.len(),
        "circuit_id": input_circuit_id
    });

    println!("{}", serde_json::to_string_pretty(&input_metadata)?);
    write_metadata(INPUT_CIRCUIT_METADATA, &input_metadata)?;
    write_remote(INPUT_PROVING_KEY, &input_proving_checksum, &input_proving_key)?;
    write_local(INPUT_VERIFYING_KEY, &input_verifying_key)?;

    Ok(())
}

/// Runs the output circuit setup.
pub fn output_setup<N: Network>() -> Result<()> {
    const OUTPUT_CIRCUIT_METADATA: &str = "output.metadata";
    const OUTPUT_PROVING_KEY: &str = "output.proving";
    const OUTPUT_VERIFYING_KEY: &str = "output.verifying";

    let (output_proving_key, output_verifying_key) =
        N::OutputSNARK::setup(&OutputCircuit::<N>::blank(), &mut SRS::CircuitSpecific(&mut thread_rng()))?;

    let output_circuit_id =
        hex::encode(N::output_circuit_id_crh().hash(&output_verifying_key.to_minimal_bits())?.to_bytes_le()?);
    let output_proving_key = output_proving_key.to_bytes_le()?;
    let output_proving_checksum = checksum(&output_proving_key);
    let output_verifying_key = output_verifying_key.to_bytes_le()?;

    let output_metadata = json!({
        "proving_checksum": output_proving_checksum,
        "proving_size": output_proving_key.len(),
        "verifying_checksum": checksum(&output_verifying_key),
        "verifying_size": output_verifying_key.len(),
        "circuit_id": output_circuit_id
    });

    println!("{}", serde_json::to_string_pretty(&output_metadata)?);
    write_metadata(OUTPUT_CIRCUIT_METADATA, &output_metadata)?;
    write_remote(OUTPUT_PROVING_KEY, &output_proving_checksum, &output_proving_key)?;
    write_local(OUTPUT_VERIFYING_KEY, &output_verifying_key)?;

    Ok(())
}

/// Runs the PoSW circuit setup.
pub fn posw_setup<N: Network>() -> Result<()> {
    const POSW_CIRCUIT_METADATA: &str = "posw.metadata";
    const POSW_PROVING_KEY: &str = "posw.proving";
    const POSW_VERIFYING_KEY: &str = "posw.verifying";

    // TODO: decide the size of the universal setup
    let max_degree =
        AHPForR1CS::<<N as Network>::InnerScalarField, MarlinHidingMode>::max_degree(40000, 40000, 60000).unwrap();
    let universal_srs = <<N as Network>::PoSWSNARK as SNARK>::universal_setup(&max_degree, &mut thread_rng())?;
    let srs_bytes = universal_srs.to_bytes_le()?;
    println!("srs\n\tsize - {}", srs_bytes.len());

    let posw = <N::PoSW as PoSWScheme<N>>::setup::<ThreadRng>(&mut SRS::<ThreadRng, _>::Universal(
        &FromBytes::read_le(&srs_bytes[..])?,
    ))?;

    let posw_proving_key = posw.proving_key().as_ref().expect("posw_proving_key is missing").to_bytes_le()?;
    let posw_proving_checksum = checksum(&posw_proving_key);
    let posw_verifying_key = posw.verifying_key().to_bytes_le()?;

    let posw_metadata = json!({
        "proving_checksum": posw_proving_checksum,
        "proving_size": posw_proving_key.len(),
        "verifying_checksum": checksum(&posw_verifying_key),
        "verifying_size": posw_verifying_key.len(),
    });

    println!("{}", serde_json::to_string_pretty(&posw_metadata)?);
    write_metadata(POSW_CIRCUIT_METADATA, &posw_metadata)?;
    write_remote(POSW_PROVING_KEY, &posw_proving_checksum, &posw_proving_key)?;
    write_local(POSW_VERIFYING_KEY, &posw_verifying_key)?;

    Ok(())
}

/// Runs the trial SRS setup. (cargo run --release --example setup trial_srs 1048576)
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
        "posw" => match args[2].as_str() {
            "testnet1" => posw_setup::<snarkvm_dpc::testnet1::Testnet1>()?,
            "testnet2" => posw_setup::<snarkvm_dpc::testnet2::Testnet2>()?,
            _ => panic!("Invalid network"),
        },
        "input" => match args[2].as_str() {
            "testnet1" => input_setup::<snarkvm_dpc::testnet1::Testnet1>()?,
            "testnet2" => input_setup::<snarkvm_dpc::testnet2::Testnet2>()?,
            _ => panic!("Invalid network"),
        },
        "output" => match args[2].as_str() {
            "testnet1" => output_setup::<snarkvm_dpc::testnet1::Testnet1>()?,
            "testnet2" => output_setup::<snarkvm_dpc::testnet2::Testnet2>()?,
            _ => panic!("Invalid network"),
        },
        "trial_srs" => trial_srs::<snarkvm_console::network::Testnet3>(args[2].as_str().parse::<usize>()?)?,
        _ => panic!("Invalid parameter"),
    };

    Ok(())
}
