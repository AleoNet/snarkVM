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

use crate::{PoseidonGrainLFSR, PrimeField};

use anyhow::{bail, Result};

/// Parameters and RNG used
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoseidonParameters<F: PrimeField, const RATE: usize, const CAPACITY: usize> {
    /// number of rounds in a full-round operation
    pub full_rounds: usize,
    /// number of rounds in a partial-round operation
    pub partial_rounds: usize,
    /// Exponent used in S-boxes
    pub alpha: u64,
    /// Additive Round keys. These are added before each MDS matrix application to make it an affine shift.
    /// They are indexed by `ark[round_num][state_element_index]`
    pub ark: Vec<Vec<F>>,
    /// Maximally Distance Separating Matrix.
    pub mds: Vec<Vec<F>>,
}

/// A field with Poseidon parameters associated
pub trait PoseidonDefaultField {
    /// Obtain the default Poseidon parameters for this rate and for this prime field,
    /// with a specific optimization goal.
    fn default_poseidon_parameters<const RATE: usize>() -> Result<PoseidonParameters<Self, RATE, 1>>
    where
        Self: PrimeField,
    {
        /// Internal function that computes the ark and mds from the Poseidon Grain LFSR.
        #[allow(clippy::type_complexity)]
        fn find_poseidon_ark_and_mds<F: PrimeField, const RATE: usize>(
            full_rounds: u64,
            partial_rounds: u64,
            skip_matrices: u64,
        ) -> Result<(Vec<Vec<F>>, Vec<Vec<F>>)> {
            let mut lfsr =
                PoseidonGrainLFSR::new(false, F::size_in_bits() as u64, (RATE + 1) as u64, full_rounds, partial_rounds);

            let mut ark = Vec::<Vec<F>>::new();
            for _ in 0..(full_rounds + partial_rounds) {
                ark.push(lfsr.get_field_elements_rejection_sampling(RATE + 1)?);
            }

            let mut mds = vec![vec![F::zero(); RATE + 1]; RATE + 1];
            for _ in 0..skip_matrices {
                let _ = lfsr.get_field_elements_mod_p::<F>(2 * (RATE + 1))?;
            }

            // A qualifying matrix must satisfy the following requirements:
            // - There is no duplication among the elements in x or y.
            // - There is no i and j such that x[i] + y[j] = p.
            // - There resultant MDS passes all three tests.

            let xs = lfsr.get_field_elements_mod_p::<F>(RATE + 1)?;
            let ys = lfsr.get_field_elements_mod_p::<F>(RATE + 1)?;

            for (i, x) in xs.iter().enumerate().take(RATE + 1) {
                for (j, y) in ys.iter().enumerate().take(RATE + 1) {
                    mds[i][j] = (*x + y).inverse().unwrap();
                }
            }

            Ok((ark, mds))
        }

        match Self::Parameters::PARAMS_OPT_FOR_CONSTRAINTS.iter().find(|entry| entry.rate == RATE) {
            Some(entry) => {
                let (ark, mds) = find_poseidon_ark_and_mds::<Self, RATE>(
                    entry.full_rounds as u64,
                    entry.partial_rounds as u64,
                    entry.skip_matrices as u64,
                )?;
                Ok(PoseidonParameters {
                    full_rounds: entry.full_rounds,
                    partial_rounds: entry.partial_rounds,
                    alpha: entry.alpha as u64,
                    ark,
                    mds,
                })
            }
            None => bail!("No Poseidon parameters were found for this rate"),
        }
    }
}

/// A trait for default Poseidon parameters associated with a prime field
pub trait PoseidonDefaultParameters {
    /// An array of the parameters optimized for constraints
    /// (rate, alpha, full_rounds, partial_rounds, skip_matrices)
    /// for rate = 2, 3, 4, 5, 6, 7, 8
    ///
    /// Here, `skip_matrices` denote how many matrices to skip before
    /// finding one that satisfy all the requirements.
    const PARAMS_OPT_FOR_CONSTRAINTS: [PoseidonDefaultParametersEntry; 7];
}

/// An entry in the default Poseidon parameters
pub struct PoseidonDefaultParametersEntry {
    /// The rate (in terms of number of field elements).
    pub rate: usize,
    /// Exponent used in S-boxes.
    pub alpha: usize,
    /// Number of rounds in a full-round operation.
    pub full_rounds: usize,
    /// Number of rounds in a partial-round operation.
    pub partial_rounds: usize,
    /// Number of matrices to skip when generating parameters using the Grain LFSR.
    ///
    /// The matrices being skipped are those that do not satisfy all the desired properties.
    /// See the [reference implementation](https://extgit.iaik.tugraz.at/krypto/hadeshash/-/blob/master/code/generate_parameters_grain.sage) for more detail.
    pub skip_matrices: usize,
}

impl PoseidonDefaultParametersEntry {
    /// Create an entry in PoseidonDefaultParameters.
    pub const fn new(
        rate: usize,
        alpha: usize,
        full_rounds: usize,
        partial_rounds: usize,
        skip_matrices: usize,
    ) -> Self {
        Self { rate, alpha, full_rounds, partial_rounds, skip_matrices }
    }
}
