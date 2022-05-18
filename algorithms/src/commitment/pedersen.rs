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

use crate::{crh::PedersenCRH, crypto_hash::hash_to_curve, CommitmentScheme, CRH};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::BitIteratorLE;

use anyhow::Result;
use itertools::Itertools;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PedersenCommitment<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    pub crh: PedersenCRH<G, NUM_WINDOWS, WINDOW_SIZE>,
    pub random_base: Vec<G>,
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CommitmentScheme
    for PedersenCommitment<G, NUM_WINDOWS, WINDOW_SIZE>
{
    type Output = G::Affine;
    type Parameters = (Vec<Vec<G>>, Vec<G>);
    type Randomness = G::ScalarField;

    fn setup(message: &str) -> Self {
        // First, compute the bases.
        let crh = PedersenCRH::setup(message);

        // Next, compute the random base.
        let (generator, _, _) = hash_to_curve::<G::Affine>(&format!("{message} for random base"));
        let mut base = generator.to_projective();

        let num_scalar_bits = G::ScalarField::size_in_bits();
        let mut random_base = Vec::with_capacity(num_scalar_bits);
        for _ in 0..num_scalar_bits {
            random_base.push(base);
            base.double_in_place();
        }
        assert_eq!(random_base.len(), num_scalar_bits);

        Self { crh, random_base }
    }

    fn commit(&self, input: &[bool], randomness: &Self::Randomness) -> Result<Self::Output> {
        let mut output = self.crh.hash(input)?.to_projective();

        // Compute h^r.
        let scalar_bits = BitIteratorLE::new(randomness.to_repr()).take(G::ScalarField::size_in_bits());
        for (bit, power) in scalar_bits.zip_eq(&self.random_base) {
            if bit {
                output += power
            }
        }

        Ok(output.to_affine())
    }

    fn parameters(&self) -> Self::Parameters {
        (self.crh.bases.clone(), self.random_base.clone())
    }
}
