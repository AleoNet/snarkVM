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

use snarkvm_algorithms::{crh::sha256::sha256, SNARK, SRS};
use snarkvm_dpc::{DPCError, InnerCircuit, Network};
use snarkvm_utilities::ToBytes;

use rand::thread_rng;
use std::path::PathBuf;

mod utils;
use utils::store;

pub fn setup<C: Network>() -> Result<(Vec<u8>, Vec<u8>), DPCError> {
    let rng = &mut thread_rng();

    let inner_snark_parameters = C::InnerSNARK::setup(&InnerCircuit::<C>::blank(), &mut SRS::CircuitSpecific(rng))?;
    let inner_snark_pk = inner_snark_parameters.0.to_bytes_le()?;
    let inner_snark_vk: <C::InnerSNARK as SNARK>::VerifyingKey = inner_snark_parameters.1.into();
    let inner_snark_vk = inner_snark_vk.to_bytes_le()?;

    println!("inner_snark_pk.params\n\tsize - {}", inner_snark_pk.len());
    println!("inner_snark_vk.params\n\tsize - {}", inner_snark_vk.len());
    Ok((inner_snark_pk, inner_snark_vk))
}

fn versioned_filename(checksum: &str) -> String {
    match checksum.get(0..7) {
        Some(sum) => format!("inner_snark_pk-{}.params", sum),
        _ => "inner_snark_pk.params".to_string(),
    }
}

pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        println!("Invalid number of arguments. Given: {} - Required: 1", args.len() - 1);
        return;
    }

    let (inner_snark_pk, inner_snark_vk) = match args[1].as_str() {
        "testnet1" => setup::<snarkvm_dpc::testnet1::Testnet1Parameters>().unwrap(),
        "testnet2" => setup::<snarkvm_dpc::testnet2::Testnet2Parameters>().unwrap(),
        _ => panic!("Invalid parameters"),
    };

    let inner_snark_pk_checksum = hex::encode(sha256(&inner_snark_pk));
    store(
        &PathBuf::from(&versioned_filename(&inner_snark_pk_checksum)),
        &PathBuf::from("inner_snark_pk.checksum"),
        &inner_snark_pk,
    )
    .unwrap();
    store(
        &PathBuf::from("inner_snark_vk.params"),
        &PathBuf::from("inner_snark_vk.checksum"),
        &inner_snark_vk,
    )
    .unwrap();
}
