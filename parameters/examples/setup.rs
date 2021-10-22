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

use snarkvm_algorithms::{crh::sha256::sha256, CRH, SNARK, SRS};
use snarkvm_dpc::{
    Execution,
    Function,
    InnerCircuit,
    Network,
    Noop,
    OuterCircuit,
    PoSWScheme,
    ProgramPublicVariables,
    SynthesizedCircuit,
};
use snarkvm_marlin::ahp::AHPForR1CS;
use snarkvm_utilities::{FromBytes, ToBytes, ToMinimalBits};

use anyhow::Result;
use rand::{prelude::ThreadRng, thread_rng};
use serde_json::{json, Value};
use std::{
    fs::File,
    io::{BufWriter, Write},
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
    file.write_all(&bytes)?;
    Ok(())
}

/// Writes the given bytes to the given filename.
fn write_local(filename: &str, bytes: &[u8]) -> Result<()> {
    let mut file = BufWriter::new(File::create(PathBuf::from(filename))?);
    file.write_all(&bytes)?;
    Ok(())
}

/// Writes the given metadata as JSON to the given filename.
fn write_metadata(filename: &str, metadata: &Value) -> Result<()> {
    let mut file = BufWriter::new(File::create(PathBuf::from(filename))?);
    file.write_all(&serde_json::to_vec_pretty(metadata)?)?;
    Ok(())
}

/// Runs a universal SRS setup.
pub fn universal_setup<N: Network>() -> Result<()> {
    const UNIVERSAL_METADATA: &str = "universal.metadata";
    const UNIVERSAL_SRS: &str = "universal.srs";

    let max_degree = AHPForR1CS::<<N as Network>::InnerScalarField>::max_degree(70000, 70000, 70000).unwrap();
    let universal_srs = <<N as Network>::ProgramSNARK as SNARK>::universal_setup(&max_degree, &mut thread_rng())?;
    let universal_srs = universal_srs.to_bytes_le()?;

    let universal_checksum = checksum(&universal_srs);
    let universal_metadata = json!({
        "srs_checksum": universal_checksum,
        "srs_size": universal_srs.len()
    });

    println!("{}", serde_json::to_string_pretty(&universal_metadata)?);
    write_metadata(UNIVERSAL_METADATA, &universal_metadata)?;
    write_remote(UNIVERSAL_SRS, &universal_checksum, &universal_srs)?;

    Ok(())
}

/// Runs the noop circuit setup.
pub fn noop_setup<N: Network>() -> Result<()> {
    const NOOP_CIRCUIT_METADATA: &str = "noop.metadata";
    const NOOP_PROVING_KEY: &str = "noop.proving";
    const NOOP_VERIFYING_KEY: &str = "noop.verifying";

    let (proving_key, verifying_key) = <N::ProgramSNARK as SNARK>::setup(
        &SynthesizedCircuit::<N>::Noop(Default::default()),
        &mut *N::program_srs(&mut thread_rng()).borrow_mut(),
    )?;

    let noop_function_id = hex::encode(<N as Network>::function_id(&verifying_key)?.to_bytes_le()?);
    let noop_proving_key = proving_key.to_bytes_le()?;
    let noop_verifying_key = verifying_key.to_bytes_le()?;

    let noop_metadata = json!({
        "proving_checksum": checksum(&noop_proving_key),
        "proving_size": noop_proving_key.len(),
        "verifying_checksum": checksum(&noop_verifying_key),
        "verifying_size": noop_verifying_key.len(),
        "circuit_id": noop_function_id,
    });

    println!("{}", serde_json::to_string_pretty(&noop_metadata)?);
    write_metadata(NOOP_CIRCUIT_METADATA, &noop_metadata)?;
    write_local(NOOP_PROVING_KEY, &noop_proving_key)?;
    write_local(NOOP_VERIFYING_KEY, &noop_verifying_key)?;

    Ok(())
}

/// Runs the inner circuit setup.
pub fn inner_setup<N: Network>() -> Result<()> {
    const INNER_CIRCUIT_METADATA: &str = "inner.metadata";
    const INNER_PROVING_KEY: &str = "inner.proving";
    const INNER_VERIFYING_KEY: &str = "inner.verifying";

    let (inner_proving_key, inner_verifying_key) = N::InnerSNARK::setup(
        &InnerCircuit::<N>::blank(),
        &mut SRS::CircuitSpecific(&mut thread_rng()),
    )?;

    let inner_circuit_id = hex::encode(
        N::inner_circuit_id_crh()
            .hash_bits(&inner_verifying_key.to_minimal_bits())?
            .to_bytes_le()?,
    );
    let inner_proving_key = inner_proving_key.to_bytes_le()?;
    let inner_proving_checksum = checksum(&inner_proving_key);
    let inner_verifying_key = inner_verifying_key.to_bytes_le()?;

    let inner_metadata = json!({
        "proving_checksum": inner_proving_checksum,
        "proving_size": inner_proving_key.len(),
        "verifying_checksum": checksum(&inner_verifying_key),
        "verifying_size": inner_verifying_key.len(),
        "circuit_id": inner_circuit_id
    });

    println!("{}", serde_json::to_string_pretty(&inner_metadata)?);
    write_metadata(INNER_CIRCUIT_METADATA, &inner_metadata)?;
    write_remote(INNER_PROVING_KEY, &inner_proving_checksum, &inner_proving_key)?;
    write_local(INNER_VERIFYING_KEY, &inner_verifying_key)?;

    Ok(())
}

/// Runs the outer circuit setup.
pub fn outer_setup<N: Network>() -> Result<()> {
    const OUTER_CIRCUIT_METADATA: &str = "outer.metadata";
    const OUTER_PROVING_KEY: &str = "outer.proving";
    const OUTER_VERIFYING_KEY: &str = "outer.verifying";

    let (inner_proof, inner_verifying_key) = match N::NETWORK_NAME {
        "testnet1" => {
            use snarkvm_parameters::testnet1::{InnerProvingKeyBytes, InnerVerifyingKeyBytes};

            let inner_proving_key =
                <N::InnerSNARK as SNARK>::ProvingKey::read_le(InnerProvingKeyBytes::load_bytes()?.as_slice())?;
            let inner_verifying_key =
                <N::InnerSNARK as SNARK>::VerifyingKey::read_le(InnerVerifyingKeyBytes::load_bytes()?.as_slice())?;
            let inner_proof = N::InnerSNARK::prove(&inner_proving_key, &InnerCircuit::<N>::blank(), &mut thread_rng())?;

            (inner_proof, inner_verifying_key)
        }
        "testnet2" => {
            use snarkvm_parameters::testnet2::{InnerProvingKeyBytes, InnerVerifyingKeyBytes};

            let inner_proving_key =
                <N::InnerSNARK as SNARK>::ProvingKey::read_le(InnerProvingKeyBytes::load_bytes()?.as_slice())?;
            let inner_verifying_key =
                <N::InnerSNARK as SNARK>::VerifyingKey::read_le(InnerVerifyingKeyBytes::load_bytes()?.as_slice())?;
            let inner_proof = N::InnerSNARK::prove(&inner_proving_key, &InnerCircuit::<N>::blank(), &mut thread_rng())?;

            (inner_proof, inner_verifying_key)
        }
        _ => panic!("Invalid network for outer setup"),
    };

    let (outer_proving_key, outer_verifying_key) = N::OuterSNARK::setup(
        &OuterCircuit::<N>::blank(inner_verifying_key, inner_proof, Execution {
            program_id: *N::noop_program_id(),
            program_path: N::noop_program_path().clone(),
            verifying_key: N::noop_circuit_verifying_key().clone(),
            proof: Noop::<N>::new().execute(ProgramPublicVariables::blank())?,
        }),
        &mut SRS::CircuitSpecific(&mut thread_rng()),
    )?;

    let outer_proving_key = outer_proving_key.to_bytes_le()?;
    let outer_proving_checksum = checksum(&outer_proving_key);
    let outer_verifying_key = outer_verifying_key.to_bytes_le()?;

    let outer_metadata = json!({
        "proving_checksum": outer_proving_checksum,
        "proving_size": outer_proving_key.len(),
        "verifying_checksum": checksum(&outer_verifying_key),
        "verifying_size": outer_verifying_key.len(),
    });

    println!("{}", serde_json::to_string_pretty(&outer_metadata)?);
    write_metadata(OUTER_CIRCUIT_METADATA, &outer_metadata)?;
    write_remote(OUTER_PROVING_KEY, &outer_proving_checksum, &outer_proving_key)?;
    write_local(OUTER_VERIFYING_KEY, &outer_verifying_key)?;

    Ok(())
}

/// Runs the PoSW circuit setup.
pub fn posw_setup<N: Network>() -> Result<()> {
    const POSW_CIRCUIT_METADATA: &str = "posw.metadata";
    const POSW_PROVING_KEY: &str = "posw.proving";
    const POSW_VERIFYING_KEY: &str = "posw.verifying";

    // TODO: decide the size of the universal setup
    let max_degree = AHPForR1CS::<<N as Network>::InnerScalarField>::max_degree(40000, 40000, 60000).unwrap();
    let universal_srs = <<N as Network>::PoSWSNARK as SNARK>::universal_setup(&max_degree, &mut thread_rng())?;
    let srs_bytes = universal_srs.to_bytes_le()?;
    println!("srs\n\tsize - {}", srs_bytes.len());

    let posw = <N::PoSW as PoSWScheme<N>>::setup::<ThreadRng>(&mut SRS::<ThreadRng, _>::Universal(
        &FromBytes::read_le(&srs_bytes[..])?,
    ))?;

    let posw_proving_key = posw
        .proving_key()
        .as_ref()
        .expect("posw_proving_key is missing")
        .to_bytes_le()?;
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

/// Run the following command to perform a setup.
/// `cargo run --example setup [parameter] [network]`
pub fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("Invalid number of arguments. Given: {} - Required: 2", args.len() - 1);
        return Ok(());
    }

    match args[1].as_str() {
        "inner" => match args[2].as_str() {
            "testnet1" => inner_setup::<snarkvm_dpc::testnet1::Testnet1>()?,
            "testnet2" => inner_setup::<snarkvm_dpc::testnet2::Testnet2>()?,
            _ => panic!("Invalid network"),
        },
        "noop" => match args[2].as_str() {
            "testnet1" => noop_setup::<snarkvm_dpc::testnet1::Testnet1>()?,
            "testnet2" => noop_setup::<snarkvm_dpc::testnet2::Testnet2>()?,
            _ => panic!("Invalid network"),
        },
        "outer" => match args[2].as_str() {
            "testnet1" => outer_setup::<snarkvm_dpc::testnet1::Testnet1>()?,
            "testnet2" => outer_setup::<snarkvm_dpc::testnet2::Testnet2>()?,
            _ => panic!("Invalid network"),
        },
        "posw" => match args[2].as_str() {
            "testnet1" => posw_setup::<snarkvm_dpc::testnet1::Testnet1>()?,
            "testnet2" => posw_setup::<snarkvm_dpc::testnet2::Testnet2>()?,
            _ => panic!("Invalid network"),
        },
        "universal" => match args[2].as_str() {
            "testnet1" => panic!("Testnet1 does not support a universal SRS"),
            "testnet2" => universal_setup::<snarkvm_dpc::testnet2::Testnet2>()?,
            _ => panic!("Invalid network"),
        },
        _ => panic!("Invalid parameter"),
    };

    Ok(())
}
