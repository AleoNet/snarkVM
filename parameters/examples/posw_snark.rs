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

use snarkvm_algorithms::{crh::sha256, SNARK, SRS};
use snarkvm_curves::{
    bls12_377::{Bls12_377, Fr},
    PairingEngine,
};
use snarkvm_dpc::{errors::DPCError, posw::PoswMarlin, testnet1::Testnet1, testnet2::Testnet2, Network};
use snarkvm_marlin::{constraints::snark::MarlinSNARK, marlin::MarlinTestnet1Mode, FiatShamirChaChaRng};
use snarkvm_polycommit::sonic_pc::SonicKZG10;
use snarkvm_utilities::{path::PathBuf, FromBytes, ToBytes};

use blake2::Blake2s;
use rand::{prelude::ThreadRng, thread_rng};

mod utils;
use utils::store;

/// Marlin proof system on PoSW
pub type Marlin<E> = MarlinSNARK<
    <E as PairingEngine>::Fr,
    <E as PairingEngine>::Fq,
    SonicKZG10<E>,
    FiatShamirChaChaRng<<E as PairingEngine>::Fr, <E as PairingEngine>::Fq, Blake2s>,
    MarlinTestnet1Mode,
    Vec<<E as PairingEngine>::Fr>,
>;

#[allow(clippy::type_complexity)]
pub fn setup<N: Network>() -> Result<(Vec<u8>, Vec<u8>, Vec<u8>), DPCError> {
    let rng = &mut thread_rng();

    // TODO: decide the size of the universal setup
    let max_degree = snarkvm_marlin::ahp::AHPForR1CS::<Fr>::max_degree(10000, 10000, 100000).unwrap();
    let srs = Marlin::<Bls12_377>::universal_setup(&max_degree, rng).unwrap();

    let srs_bytes = srs.to_bytes_le()?;
    let posw_snark = PoswMarlin::<N>::setup::<ThreadRng>(&mut SRS::<ThreadRng, _>::Universal(
        &FromBytes::read_le(&srs_bytes[..]).unwrap(),
    ))
    .expect("could not setup params");

    let posw_snark_pk = posw_snark
        .proving_key
        .expect("posw_snark_pk should be populated")
        .to_bytes_le()?;
    let posw_snark_vk = posw_snark.verifying_key;
    let posw_snark_vk = posw_snark_vk.to_bytes_le()?;

    println!("posw_snark_pk.params\n\tsize - {}", posw_snark_pk.len());
    println!("posw_snark_vk.params\n\tsize - {}", posw_snark_vk.len());
    println!("srs\n\tsize - {}", srs_bytes.len());
    Ok((posw_snark_pk, posw_snark_vk, srs_bytes))
}

fn versioned_filename(checksum: &str) -> String {
    match checksum.get(0..7) {
        Some(sum) => format!("posw_snark_pk-{}.params", sum),
        _ => "posw_snark_pk.params".to_string(),
    }
}

pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        println!("Invalid number of arguments. Given: {} - Required: 1", args.len() - 1);
        return;
    }

    let (posw_snark_pk, posw_snark_vk, _srs) = match args[1].as_str() {
        "testnet1" => setup::<Testnet1>().unwrap(),
        "testnet2" => setup::<Testnet2>().unwrap(),
        _ => panic!("Invalid network"),
    };

    let posw_snark_pk_checksum = hex::encode(sha256(&posw_snark_pk));
    store(
        &PathBuf::from(&versioned_filename(&posw_snark_pk_checksum)),
        &PathBuf::from("posw_snark_pk.checksum"),
        &posw_snark_pk,
    )
    .unwrap();
    store(
        &PathBuf::from("posw_snark_vk.params"),
        &PathBuf::from("posw_snark_vk.checksum"),
        &posw_snark_vk,
    )
    .unwrap();
}
