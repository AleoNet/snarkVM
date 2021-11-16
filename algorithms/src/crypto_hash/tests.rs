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

use crate::crypto_hash::{CryptographicSponge, PoseidonDefaultParametersField, PoseidonGrainLFSR, PoseidonSponge};
use snarkvm_curves::bls12_377::Fr;

use itertools::Itertools;
use std::{
    path::{PathBuf, MAIN_SEPARATOR},
    sync::Arc,
};

#[track_caller]
fn expect_file_with_name(name: impl ToString, val: impl std::fmt::Debug) {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR").to_string());
    path.push(".snapshot");
    if !path.exists() {
        std::fs::create_dir_all(&path).expect("failed to create directory");
    }
    let loc = std::panic::Location::caller();
    let line = loc.line().to_string();
    let column = loc.column().to_string();
    let file_name: String = module_path!()
        .split("::")
        .chain([line.as_str(), column.as_str(), &name.to_string()])
        .join("_");
    path.push(file_name);
    path.set_extension("snap");
    if !path.exists() {
        std::fs::File::create(&path).expect("failed to create file");
    }
    expect_test::expect_file![path].assert_eq(&format!("{:?}", val));
}

#[track_caller]
fn expect_file(val: impl std::fmt::Debug) {
    expect_file_with_name("", val)
}

#[test]
fn test_grain_lfsr_consistency() {
    let mut lfsr = PoseidonGrainLFSR::new(false, 253, 3, 8, 31);
    expect_file(lfsr.get_field_elements_rejection_sampling::<Fr>(1));
    expect_file(lfsr.get_field_elements_rejection_sampling::<Fr>(1));
}

#[test]
fn test_poseidon_sponge_consistency() {
    let sponge_param = Arc::new(Fr::get_default_poseidon_parameters::<2>(false).unwrap());
    for absorb in 0..10 {
        for squeeze in 1..10 {
            let mut sponge = PoseidonSponge::<Fr, 2, 1>::new(&sponge_param);
            sponge.absorb(&vec![Fr::from(1237812u64); absorb]);
            expect_file_with_name(
                format!("Absorb {} -> Squeeze {}", absorb, squeeze),
                sponge.squeeze_field_elements(squeeze),
            );
        }
    }
}

#[test]
fn bls12_377_fr_poseidon_default_parameters_test() {
    // Optimize for constraints
    let constraints_rate_2 = Fr::get_default_poseidon_parameters::<2>(false).unwrap();
    expect_file(constraints_rate_2.ark);
    expect_file(constraints_rate_2.mds);

    let constraints_rate_3 = Fr::get_default_poseidon_parameters::<3>(false).unwrap();
    expect_file(constraints_rate_3.ark);
    expect_file(constraints_rate_3.mds);

    let constraints_rate_4 = Fr::get_default_poseidon_parameters::<4>(false).unwrap();
    expect_file(constraints_rate_4.ark);
    expect_file(constraints_rate_4.mds);

    let constraints_rate_5 = Fr::get_default_poseidon_parameters::<5>(false).unwrap();
    expect_file(constraints_rate_5.ark);
    expect_file(constraints_rate_5.mds);

    let constraints_rate_6 = Fr::get_default_poseidon_parameters::<6>(false).unwrap();
    expect_file(constraints_rate_6.ark);
    expect_file(constraints_rate_6.mds);

    let constraints_rate_7 = Fr::get_default_poseidon_parameters::<7>(false).unwrap();
    expect_file(constraints_rate_7.ark);
    expect_file(constraints_rate_7.mds);

    let constraints_rate_8 = Fr::get_default_poseidon_parameters::<8>(false).unwrap();
    expect_file(constraints_rate_8.ark);
    expect_file(constraints_rate_8.mds);

    // weights
    let weights_rate_2 = Fr::get_default_poseidon_parameters::<2>(true).unwrap();
    expect_file(weights_rate_2.ark);
    expect_file(weights_rate_2.mds);

    let weights_rate_3 = Fr::get_default_poseidon_parameters::<3>(true).unwrap();
    expect_file(weights_rate_3.ark);
    expect_file(weights_rate_3.mds);

    let weights_rate_4 = Fr::get_default_poseidon_parameters::<4>(true).unwrap();
    expect_file(weights_rate_4.ark);
    expect_file(weights_rate_4.mds);

    let weights_rate_5 = Fr::get_default_poseidon_parameters::<5>(true).unwrap();
    expect_file(weights_rate_5.ark);
    expect_file(weights_rate_5.mds);

    let weights_rate_6 = Fr::get_default_poseidon_parameters::<6>(true).unwrap();
    expect_file(weights_rate_6.ark);
    expect_file(weights_rate_6.mds);

    let weights_rate_7 = Fr::get_default_poseidon_parameters::<7>(true).unwrap();
    expect_file(weights_rate_7.ark);
    expect_file(weights_rate_7.mds);

    let weights_rate_8 = Fr::get_default_poseidon_parameters::<8>(true).unwrap();
    expect_file(weights_rate_8.ark);
    expect_file(weights_rate_8.mds);
}
