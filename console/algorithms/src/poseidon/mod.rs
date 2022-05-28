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

mod helpers;

mod hash;
mod hash_many;
mod hash_to_scalar;
mod prf;

use crate::{poseidon::helpers::*, Hash, HashMany, HashToScalar, PRF};
use snarkvm_fields::{PoseidonParameters, PrimeField};

use anyhow::{bail, Result};
use std::sync::Arc;

const CAPACITY: usize = 1;

/// Poseidon2 is a cryptographic hash function of input rate 2.
pub type Poseidon2<F> = Poseidon<F, 2>;
/// Poseidon4 is a cryptographic hash function of input rate 4.
pub type Poseidon4<F> = Poseidon<F, 4>;
/// Poseidon8 is a cryptographic hash function of input rate 8.
pub type Poseidon8<F> = Poseidon<F, 8>;

#[derive(Clone)]
pub struct Poseidon<F: PrimeField, const RATE: usize> {
    /// The Poseidon parameters for hashing.
    parameters: Arc<PoseidonParameters<F, RATE, CAPACITY>>,
}

impl<F: PrimeField, const RATE: usize> Poseidon<F, RATE> {
    /// Initializes a new instance of Poseidon.
    pub fn setup() -> Result<Self> {
        Ok(Self { parameters: Arc::new(F::default_poseidon_parameters::<RATE>()?) })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::edwards_bls12::Fq;
    use snarkvm_fields::{PoseidonDefaultField, PoseidonGrainLFSR};

    use core::fmt::Debug;
    use std::{path::PathBuf, sync::Arc};

    /// Returns the path to the `resources` folder for this module.
    fn resources_path() -> PathBuf {
        // Construct the path for the `resources` folder.
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.push("src");
        path.push("poseidon");
        path.push("resources");

        // Create the `resources` folder, if it does not exist.
        if !path.exists() {
            std::fs::create_dir_all(&path).unwrap_or_else(|_| panic!("Failed to create resources folder: {:?}", path));
        }
        // Output the path.
        path
    }

    /// Loads the given `test_folder/test_file` and asserts the given `candidate` matches the expected values.
    #[track_caller]
    fn assert_snapshot<S1: Into<String>, S2: Into<String>, C: Debug>(test_folder: S1, test_file: S2, candidate: C) {
        // Construct the path for the test folder.
        let mut path = resources_path();
        path.push(test_folder.into());

        // Create the test folder, if it does not exist.
        if !path.exists() {
            std::fs::create_dir(&path).unwrap_or_else(|_| panic!("Failed to create test folder: {:?}", path));
        }

        // Construct the path for the test file.
        path.push(test_file.into());
        path.set_extension("snap");

        // Create the test file, if it does not exist.
        if !path.exists() {
            std::fs::File::create(&path).unwrap_or_else(|_| panic!("Failed to create file: {:?}", path));
        }

        // Assert the test file is equal to the expected value.
        expect_test::expect_file![path].assert_eq(&format!("{:?}", candidate));
    }

    #[test]
    fn test_grain_lfsr() -> Result<()> {
        let mut lfsr = PoseidonGrainLFSR::new(false, 253, 3, 8, 31);
        assert_snapshot("test_grain_lfsr", "first_sample", lfsr.get_field_elements_rejection_sampling::<Fq>(1)?);
        assert_snapshot("test_grain_lfsr", "second_sample", lfsr.get_field_elements_rejection_sampling::<Fq>(1)?);
        Ok(())
    }

    #[test]
    fn test_sponge() {
        const RATE: usize = 2;
        let parameters = Arc::new(Fq::default_poseidon_parameters::<RATE>().unwrap());

        for absorb in 0..10 {
            for squeeze in 0..10 {
                let iteration = format!("absorb_{absorb}_squeeze_{squeeze}");

                let mut sponge = PoseidonSponge::<Fq, RATE, CAPACITY>::new(&parameters);
                sponge.absorb(&vec![Fq::from(1237812u64); absorb]);

                let next_absorb_index = if absorb % RATE != 0 || absorb == 0 { absorb % RATE } else { RATE };
                assert_eq!(sponge.mode, DuplexSpongeMode::Absorbing { next_absorb_index }, "{iteration}");

                assert_snapshot("test_sponge", &iteration, sponge.squeeze(squeeze as u16));

                let next_squeeze_index = if squeeze % RATE != 0 || squeeze == 0 { squeeze % RATE } else { RATE };
                match squeeze == 0 {
                    true => assert_eq!(sponge.mode, DuplexSpongeMode::Absorbing { next_absorb_index }, "{iteration}"),
                    false => assert_eq!(sponge.mode, DuplexSpongeMode::Squeezing { next_squeeze_index }, "{iteration}"),
                }
            }
        }
    }

    #[test]
    fn test_parameters() {
        fn single_rate_test<const RATE: usize>() {
            let parameters = Fq::default_poseidon_parameters::<RATE>().unwrap();
            assert_snapshot("test_parameters", format!("rate_{RATE}_ark"), parameters.ark);
            assert_snapshot("test_parameters", format!("rate_{RATE}_mds"), parameters.mds);
        }
        // Optimized for constraints.
        single_rate_test::<2>();
        single_rate_test::<3>();
        single_rate_test::<4>();
        single_rate_test::<5>();
        single_rate_test::<6>();
        single_rate_test::<7>();
        single_rate_test::<8>();
    }
}
