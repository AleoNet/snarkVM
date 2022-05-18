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

mod commit;
mod commit_uncompressed;
mod hash;
mod hash_uncompressed;

use crate::algorithms::{Commit, CommitUncompressed, Hash, HashUncompressed};
use snarkvm_algorithms::crypto_hash::hash_to_curve;
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::ToBits;

use anyhow::{bail, Result};
use itertools::Itertools;
use std::borrow::Cow;

/// Pedersen is a collision-resistant hash function that takes a variable-length input.
/// The Pedersen hash function does *not* behave like a random oracle, see Poseidon for one.
pub struct Pedersen<G: ProjectiveCurve, const NUM_BITS: usize> {
    /// The base window for the Pedersen hash.
    bases: [G; NUM_BITS],
    /// The random base window for the Pedersen commitment.
    random_base: Vec<G>,
}

impl<G: ProjectiveCurve, const NUM_BITS: usize> Pedersen<G, NUM_BITS> {
    /// Initializes a new instance of Pedersen with the given setup message.
    pub fn setup(message: &str) -> Self {
        // Construct an indexed message to attempt to sample a base.
        let (generator, _, _) = hash_to_curve::<G::Affine>(&format!("Pedersen.Base.{message}"));
        let mut base = generator.to_projective();
        let mut bases = [G::zero(); NUM_BITS];
        for i in 0..NUM_BITS {
            bases[i] = base;
            base.double_in_place();
        }

        // Next, compute the random base.
        let (generator, _, _) = hash_to_curve::<G::Affine>(&format!("Pedersen.RandomBase.{message}"));
        let mut base = generator.to_projective();
        let num_scalar_bits = G::ScalarField::size_in_bits();
        let mut random_base = Vec::with_capacity(num_scalar_bits);
        for _ in 0..num_scalar_bits {
            random_base.push(base);
            base.double_in_place();
        }
        assert_eq!(random_base.len(), num_scalar_bits);

        Self { bases, random_base }
    }
}
