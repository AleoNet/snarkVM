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

use snarkvm_algorithms::prelude::*;
use snarkvm_dpc::{DPCError, Network, SynthesizedCircuit};
use snarkvm_utilities::ToBytes;

use rand::thread_rng;
use std::path::PathBuf;

mod utils;
use utils::store;

pub fn setup<N: Network>() -> Result<(Vec<u8>, Vec<u8>), DPCError> {
    let rng = &mut thread_rng();

    // Compute the proving key and verifying key.
    let (proving_key, verifying_key) = <N::ProgramSNARK as SNARK>::setup(
        &SynthesizedCircuit::<N>::Noop(Default::default()),
        &mut *N::program_srs(rng).borrow_mut(),
    )?;

    // Compute the circuit ID.
    let circuit_id = <N as Network>::program_circuit_id(&verifying_key)?;

    let noop_program_snark_pk = proving_key.to_bytes_le()?;
    let noop_program_snark_vk = verifying_key.to_bytes_le()?;

    println!("noop_program_snark_pk.params\n\tsize - {}", noop_program_snark_pk.len());
    println!("noop_program_snark_vk.params\n\tsize - {}", noop_program_snark_vk.len());
    Ok((noop_program_snark_pk, noop_program_snark_vk))
}

pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        println!("Invalid number of arguments. Given: {} - Required: 1", args.len() - 1);
        return;
    }

    let (program_snark_pk, program_snark_vk) = match args[1].as_str() {
        "testnet1" => setup::<snarkvm_dpc::testnet1::Testnet1>().unwrap(),
        "testnet2" => setup::<snarkvm_dpc::testnet2::Testnet2>().unwrap(),
        _ => panic!("Invalid parameters"),
    };

    store(
        &PathBuf::from("noop_program_snark_pk.params"),
        &PathBuf::from("noop_program_snark_pk.checksum"),
        &program_snark_pk,
    )
    .unwrap();
    store(
        &PathBuf::from("noop_program_snark_vk.params"),
        &PathBuf::from("noop_program_snark_vk.checksum"),
        &program_snark_vk,
    )
    .unwrap();
}
