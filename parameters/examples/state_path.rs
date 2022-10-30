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
use snarkvm_console::{
    account::PrivateKey,
    network::{Network, Testnet3},
    prelude::{One, ToBits},
    program::{BlockTree, Identifier, StatePath, STATE_PATH_FUNCTION_NAME},
    types::Field,
};
use snarkvm_synthesizer::{
    inject_and_verify_state_path,
    snark::UniversalSRS,
    Block,
    ConsensusMemory,
    ConsensusStore,
    VM,
};

use anyhow::{anyhow, Result};
use rand::thread_rng;
use serde_json::{json, Value};
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

/// Returns a new (commitment, state_path) pair.
pub fn sample_state_path<N: Network>() -> Result<(Field<N>, StatePath<N>)> {
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

    Ok((*commitment, state_path))
}

/// Synthesizes the circuit keys for the state path circuit. (cargo run --release --example state_path [network])
pub fn state_path<N: Network, A: Aleo<Network = N>>() -> Result<()> {
    // Sample a new state path.
    let (commitment, state_path) = sample_state_path::<N>()?;

    // Construct the assignment.
    let assignment = {
        // Ensure the circuit environment is clean.
        A::reset();
        // Inject and verify the state path.
        inject_and_verify_state_path::<N, A>(state_path.clone(), commitment);
        // Eject and return the assignment.
        A::eject_assignment_and_reset()
    };

    // Load the universal SRS.
    let universal_srs = UniversalSRS::<N>::load()?;

    // Synthesize the proving and verifying key.
    let state_path_function_name = Identifier::from_str(STATE_PATH_FUNCTION_NAME)?;
    let (proving_key, verifying_key) = universal_srs.to_circuit_key(&state_path_function_name, &assignment)?;

    // Ensure the proving key and verifying keys are valid.
    let proof = proving_key.prove(&state_path_function_name, &assignment, &mut thread_rng())?;
    assert!(verifying_key.verify(&state_path_function_name, &[N::Field::one(), **state_path.state_root()], &proof));

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
