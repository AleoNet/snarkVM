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

use crate::{Blake2Xs, Commit, CommitUncompressed, Hash, HashUncompressed};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::{PrimeField, Zero};
use snarkvm_utilities::{cfg_iter, BigInteger, ToBits};

use anyhow::{bail, Result};
use core::ops::Neg;
use itertools::Itertools;

pub const BHP_CHUNK_SIZE: usize = 3;
pub const BHP_LOOKUP_SIZE: usize = 2usize.pow(BHP_CHUNK_SIZE as u32);

/// BHP256 is a collision-resistant hash function that takes a 256-bit input.
pub type BHP256<G> = BHP<G, 2, 43>;
/// BHP512 is a collision-resistant hash function that takes a 512-bit input.
pub type BHP512<G> = BHP<G, 3, 57>;
/// BHP768 is a collision-resistant hash function that takes a 768-bit input.
pub type BHP768<G> = BHP<G, 6, 43>;
/// BHP1024 is a collision-resistant hash function that takes a 1024-bit input.
pub type BHP1024<G> = BHP<G, 6, 57>;

/// BHP is a collision-resistant hash function that takes a variable-length input.
/// The BHP hash function does *not* behave like a random oracle, see Poseidon for one.
pub struct BHP<G: AffineCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    /// The bases for the BHP hash.
    bases: Vec<Vec<G::Projective>>,
    /// The bases lookup table for the BHP hash.
    bases_lookup: Vec<Vec<[G::Projective; BHP_LOOKUP_SIZE]>>,
    /// The random base for the BHP commitment.
    random_base: Vec<G::Projective>,
}

impl<G: AffineCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> BHP<G, NUM_WINDOWS, WINDOW_SIZE> {
    /// Initializes a new instance of BHP with the given setup message.
    pub fn setup(message: &str) -> Self {
        // Calculate the maximum window size.
        let mut maximum_window_size = 0;
        let mut range = <G::ScalarField as PrimeField>::BigInteger::from(2_u64);
        while range < G::ScalarField::modulus_minus_one_div_two() {
            // range < (p-1)/2
            range.muln(4); // range * 2^4
            maximum_window_size += 1;
        }
        assert!(WINDOW_SIZE <= maximum_window_size, "The maximum BHP window size is {maximum_window_size}");

        // Compute the bases.
        let bases = (0..NUM_WINDOWS)
            .map(|index| {
                // Construct an indexed message to attempt to sample a base.
                let (generator, _, _) = Blake2Xs::hash_to_curve::<G>(&format!("Aleo.BHP.Base.{message}.{index}"));
                let mut base = generator.to_projective();
                // Compute the generators for the sampled base.
                let mut powers = Vec::with_capacity(WINDOW_SIZE);
                for _ in 0..WINDOW_SIZE {
                    powers.push(base);
                    for _ in 0..4 {
                        base.double_in_place();
                    }
                }
                powers
            })
            .collect::<Vec<Vec<G::Projective>>>();
        debug_assert_eq!(bases.len(), NUM_WINDOWS, "Incorrect number of windows ({:?}) for BHP", bases.len());
        bases.iter().for_each(|window| debug_assert_eq!(window.len(), WINDOW_SIZE));

        // Compute the bases lookup.
        let bases_lookup = cfg_iter!(bases)
            .map(|x| {
                x.iter()
                    .map(|g| {
                        let mut lookup = [G::Projective::zero(); BHP_LOOKUP_SIZE];
                        for (i, element) in lookup.iter_mut().enumerate().take(BHP_LOOKUP_SIZE) {
                            *element = *g;
                            if (i & 0x01) != 0 {
                                *element += g;
                            }
                            if (i & 0x02) != 0 {
                                *element += g.double();
                            }
                            if (i & 0x04) != 0 {
                                *element = element.neg();
                            }
                        }
                        lookup
                    })
                    .collect()
            })
            .collect::<Vec<Vec<[G::Projective; BHP_LOOKUP_SIZE]>>>();
        debug_assert_eq!(bases_lookup.len(), NUM_WINDOWS);
        bases_lookup.iter().for_each(|bases| debug_assert_eq!(bases.len(), WINDOW_SIZE));

        // Next, compute the random base.
        let (generator, _, _) = Blake2Xs::hash_to_curve::<G>(&format!("Aleo.BHP.RandomBase.{message}"));
        let mut base_power = generator.to_projective();
        let num_scalar_bits = G::ScalarField::size_in_bits();
        let mut random_base = Vec::with_capacity(num_scalar_bits);
        for _ in 0..num_scalar_bits {
            random_base.push(base_power);
            base_power.double_in_place();
        }
        assert_eq!(random_base.len(), num_scalar_bits);

        Self { bases, bases_lookup, random_base }
    }

    /// Returns the bases.
    pub fn bases(&self) -> &[Vec<G::Projective>] {
        &self.bases
    }

    /// Returns the random base window.
    pub fn random_base(&self) -> &[G::Projective] {
        &self.random_base
    }
}
