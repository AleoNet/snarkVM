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

use crate::{crypto_hash::PoseidonSponge, AlgebraicSponge, DuplexSpongeMode};
use snarkvm_curves::bls12_377::Fr;
use snarkvm_fields::{PoseidonDefaultField, PoseidonGrainLFSR};

use anyhow::Result;
use itertools::Itertools;
use std::{path::PathBuf, sync::Arc};

#[track_caller]
fn expect_file_with_name(name: impl ToString, val: impl std::fmt::Debug) {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR").to_string());
    path.push("src");
    path.push("crypto_hash");
    path.push("resources");
    path.push("poseidon");
    if !path.exists() {
        std::fs::create_dir_all(&path).expect("failed to create directory");
    }
    let file_name: String = module_path!().split("::").chain([name.to_string().as_ref()]).join("_");
    path.push(file_name);
    path.set_extension("snap");
    if !path.exists() {
        std::fs::File::create(&path).expect("failed to create file");
    }
    expect_test::expect_file![path].assert_eq(&format!("{:?}", val));
}

#[test]
fn test_grain_lfsr_consistency() -> Result<()> {
    let mut lfsr = PoseidonGrainLFSR::new(false, 253, 3, 8, 31);
    expect_file_with_name("first sample", lfsr.get_field_elements_rejection_sampling::<Fr>(1)?);
    expect_file_with_name("second sample", lfsr.get_field_elements_rejection_sampling::<Fr>(1)?);
    Ok(())
}

#[test]
fn test_poseidon_sponge_consistency() {
    const RATE: usize = 2;
    let sponge_param = Arc::new(Fr::default_poseidon_parameters::<RATE>().unwrap());
    for absorb in 0..10 {
        for squeeze in 0..10 {
            let iteration_name = format!("Absorb {} and Squeeze {}", absorb, squeeze);
            let mut sponge = PoseidonSponge::<Fr, RATE, 1>::new(&sponge_param);
            sponge.absorb(&vec![Fr::from(1237812u64); absorb]);
            let next_absorb_index = if absorb % RATE != 0 || absorb == 0 { absorb % RATE } else { RATE };
            assert_eq!(sponge.mode, DuplexSpongeMode::Absorbing { next_absorb_index }, "{}", iteration_name);
            expect_file_with_name(&iteration_name, sponge.squeeze(squeeze));
            let next_squeeze_index = if squeeze % RATE != 0 || squeeze == 0 { squeeze % RATE } else { RATE };
            if squeeze == 0 {
                assert_eq!(sponge.mode, DuplexSpongeMode::Absorbing { next_absorb_index }, "{}", iteration_name);
            } else {
                assert_eq!(sponge.mode, DuplexSpongeMode::Squeezing { next_squeeze_index }, "{}", iteration_name);
            }
        }
    }
}

#[test]
fn bls12_377_fr_poseidon_default_parameters_test() {
    fn single_rate_test<const RATE: usize>() {
        let params = Fr::default_poseidon_parameters::<RATE>().unwrap();
        let name = format!("rate {} and optimize_for_weights false", RATE);
        expect_file_with_name("Ark for ".to_string() + &name, params.ark);
        expect_file_with_name("MDS for ".to_string() + &name, params.mds);
    }
    // Optimize for constraints
    single_rate_test::<2>();
    single_rate_test::<3>();
    single_rate_test::<4>();
    single_rate_test::<5>();
    single_rate_test::<6>();
    single_rate_test::<7>();
    single_rate_test::<8>();
}
