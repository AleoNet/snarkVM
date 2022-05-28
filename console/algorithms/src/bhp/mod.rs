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

pub mod hasher;
use hasher::BHPHasher;

mod commit;
mod commit_uncompressed;
mod hash;
mod hash_uncompressed;

use crate::{Commit, CommitUncompressed, Hash, HashUncompressed};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::ToBits;

use anyhow::{ensure, Result};
use itertools::Itertools;
use std::sync::Arc;

const BHP_CHUNK_SIZE: usize = 3;

/// BHP256 is a collision-resistant hash function that takes a 256-bit input.
pub type BHP256<G> = BHP<G, 3, 57>; // Supports inputs up to 261 bits (1 u8 + 1 Fq).
/// BHP512 is a collision-resistant hash function that takes a 512-bit input.
pub type BHP512<G> = BHP<G, 6, 43>; // Supports inputs up to 522 bits (2 u8 + 2 Fq).
/// BHP768 is a collision-resistant hash function that takes a 768-bit input.
pub type BHP768<G> = BHP<G, 15, 23>; // Supports inputs up to 783 bits (3 u8 + 3 Fq).
/// BHP1024 is a collision-resistant hash function that takes a 1024-bit input.
pub type BHP1024<G> = BHP<G, 8, 54>; // Supports inputs up to 1044 bits (4 u8 + 4 Fq).

/// BHP is a collision-resistant hash function that takes a variable-length input.
/// The BHP hash function does *not* behave like a random oracle, see Poseidon for one.
///
/// ## Design
/// The BHP hash function splits the given input into blocks, and processes them iteratively.
///
/// The first iteration is initialized as follows:
/// ```text
/// DIGEST_0 = BHP([ 0...0 || DOMAIN || LENGTH(INPUT) || INPUT[0..BLOCK_SIZE] ]);
/// ```
/// Each subsequent iteration is initialized as follows:
/// ```text
/// DIGEST_N+1 = BHP([ DIGEST_N[0..DATA_BITS] || INPUT[(N+1)*BLOCK_SIZE..(N+2)*BLOCK_SIZE] ]);
/// ```
#[derive(Clone)]
pub struct BHP<G: AffineCurve, const NUM_WINDOWS: u8, const WINDOW_SIZE: u8> {
    /// The domain separator for the BHP hash function.
    domain: Vec<bool>,
    /// The internal BHP hasher used to process one iteration.
    hasher: BHPHasher<G, NUM_WINDOWS, WINDOW_SIZE>,
}

impl<G: AffineCurve, const NUM_WINDOWS: u8, const WINDOW_SIZE: u8> BHP<G, NUM_WINDOWS, WINDOW_SIZE>
where
    <G as AffineCurve>::BaseField: PrimeField,
{
    /// Initializes a new instance of BHP with the given domain.
    pub fn setup(domain: &str) -> Result<Self> {
        // Ensure the given domain is within the allowed size in bits.
        let num_bits = domain.len().saturating_mul(8);
        let max_bits = G::BaseField::size_in_data_bits() - 64; // 64 bits encode the length.
        ensure!(num_bits <= max_bits, "Domain cannot exceed {max_bits} bits, found {num_bits} bits");

        // Initialize the BHP hasher.
        let hasher = BHPHasher::<G, NUM_WINDOWS, WINDOW_SIZE>::setup(domain)?;

        // Convert the domain into a boolean vector.
        let mut domain = domain.as_bytes().to_bits_le();
        // Pad the domain with zeros up to the maximum size in bits.
        domain.resize(max_bits, false);
        // Reverse the domain so that it is: [ 0...0 || DOMAIN ].
        // (For advanced users): This optimizes the initial costs during hashing.
        domain.reverse();

        Ok(Self { domain, hasher })
    }

    /// Returns the domain separator for the BHP hash function.
    pub fn domain(&self) -> &[bool] {
        &self.domain
    }

    /// Returns the bases.
    pub fn bases(&self) -> &Arc<Vec<Vec<G::Projective>>> {
        self.hasher.bases()
    }

    /// Returns the random base window.
    pub fn random_base(&self) -> &Arc<Vec<G::Projective>> {
        self.hasher.random_base()
    }

    /// Returns the number of windows.
    pub fn num_windows(&self) -> u8 {
        NUM_WINDOWS
    }

    /// Returns the window size.
    pub fn window_size(&self) -> u8 {
        WINDOW_SIZE
    }
}
