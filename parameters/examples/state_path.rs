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
use snarkvm_circuit::{Aleo, Assignment};
use snarkvm_console::{
    account::PrivateKey,
    network::{Network, Testnet3},
    prelude::{One, ToBits, Zero},
    program::{BlockTree, Identifier, StatePath, STATE_PATH_FUNCTION_NAME},
    types::Field,
};
use snarkvm_synthesizer::{
    inject_and_verify_state_path,
    snark::UniversalSRS,
    Block,
    ConsensusMemory,
    ConsensusStore,
    Origin,
    VM,
};

use anyhow::{anyhow, Result};
use rand::thread_rng;
use serde_json::{json, Value};
use snarkvm_console::program::{Plaintext, Record};
use snarkvm_utilities::ToBytes;
use std::{
    fs::File,
    io::{BufWriter, Write},
    path::PathBuf,
    str::FromStr,
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

/// Returns the assignment for verifying the state path.
pub fn sample_assignment<N: Network, A: Aleo<Network = N>>() -> Result<(Assignment<N::Field>, StatePath<N>, Field<N>)> {
    // Initialize the consensus store.
    let store = ConsensusStore::<N, ConsensusMemory<N>>::open(None)?;
    // Initialize a new VM.
    let mut vm = VM::from(store)?;

    // Initialize an RNG.
    let rng = &mut thread_rng();
    // Initialize a new caller.
    let caller_private_key = PrivateKey::<N>::new(rng).unwrap();
    // Return the block.
    let genesis_block = Block::genesis(&vm, &caller_private_key, rng)?;

    // Initialize the block tree.
    let block_tree: BlockTree<N> = N::merkle_tree_bhp(&[genesis_block.hash().to_bits_le()])?;
    let block_path = block_tree.prove(genesis_block.height() as usize, &genesis_block.hash().to_bits_le())?;
    // Add the genesis block to the block tree.
    vm.block_store().insert(*block_tree.root(), block_path, &genesis_block)?;

    // Update the VM.
    for transaction in genesis_block.transactions().values() {
        vm.finalize(transaction)?;
    }

    // Fetch the first commitment.
    let commitment = genesis_block.commitments().next().ok_or_else(|| anyhow!("No commitments found"))?;
    // Compute the state path for the commitment.
    let state_path = vm.block_store().get_state_path_for_commitment(commitment, Some(&block_tree))?;

    // Compute the generator `H` as `HashToGroup(commitment)`.
    let h = N::hash_to_group_psd2(&[N::serial_number_domain(), *commitment])?;
    // Compute `gamma` as `sk_sig * H`.
    let gamma = h * caller_private_key.sk_sig();
    // Compute the serial number.
    let serial_number = Record::<N, Plaintext<N>>::serial_number_from_gamma(&gamma, *commitment)?;

    // Construct the assignment for the state path verification.
    let assignment = inject_and_verify_state_path::<N, A>(
        state_path.clone(),
        *commitment,
        gamma,
        serial_number,
        Field::zero(),
        true,
    )?;

    Ok((assignment, state_path, serial_number))
}

/// Synthesizes the circuit keys for the state path circuit. (cargo run --release --example state_path [network])
pub fn state_path<N: Network, A: Aleo<Network = N>>() -> Result<()> {
    // Load the universal SRS.
    let universal_srs = UniversalSRS::<N>::load()?;

    // Sample the assignment for the state path verification.
    let (assignment, state_path, serial_number) = sample_assignment::<N, A>()?;

    // Synthesize the proving and verifying key.
    let state_path_function_name = Identifier::from_str(STATE_PATH_FUNCTION_NAME)?;
    let (proving_key, verifying_key) = universal_srs.to_circuit_key(&state_path_function_name, &assignment)?;

    // Ensure the proving key and verifying keys are valid.
    let proof = proving_key.prove(&state_path_function_name, &assignment, &mut thread_rng())?;
    assert!(verifying_key.verify(
        &state_path_function_name,
        &Origin::StateRoot(state_path.global_state_root()).verifier_inputs(&serial_number),
        &proof
    ));

    // Initialize a vector for the commands.
    let mut commands = vec![];

    let proving_key_bytes = proving_key.to_bytes_le()?;
    let proving_key_checksum = checksum(&proving_key_bytes);

    let verifying_key_bytes = verifying_key.to_bytes_le()?;
    let verifying_key_checksum = checksum(&verifying_key_bytes);

    let metadata = json!({
        "prover_checksum": proving_key_checksum,
        "prover_size": proving_key_bytes.len(),
        "verifier_checksum": verifying_key_checksum,
        "verifier_size": verifying_key_bytes.len(),
    });

    println!("{}", serde_json::to_string_pretty(&metadata)?);
    write_metadata(&format!("{STATE_PATH_FUNCTION_NAME}.metadata"), &metadata)?;
    write_remote(&format!("{STATE_PATH_FUNCTION_NAME}.prover"), &proving_key_checksum, &proving_key_bytes)?;
    write_remote(&format!("{STATE_PATH_FUNCTION_NAME}.verifier"), &verifying_key_checksum, &verifying_key_bytes)?;

    commands.push(format!(
        "snarkup upload \"{}\"",
        versioned_filename(&format!("{STATE_PATH_FUNCTION_NAME}.prover"), &proving_key_checksum)
    ));
    commands.push(format!(
        "snarkup upload \"{}\"",
        versioned_filename(&format!("{STATE_PATH_FUNCTION_NAME}.verifier"), &verifying_key_checksum)
    ));

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

/// Run the following command to generate the state path circuit keys.
/// `cargo run --example state_path [network]`
pub fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        println!("Invalid number of arguments. Given: {} - Required: 1", args.len() - 1);
        return Ok(());
    }

    match args[1].as_str() {
        "testnet3" => {
            state_path::<Testnet3, snarkvm_circuit::AleoV0>()?;
        }
        _ => panic!("Invalid network"),
    };

    Ok(())
}
