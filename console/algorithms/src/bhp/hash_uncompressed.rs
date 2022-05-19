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

use super::*;

impl<G: AffineCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> HashUncompressed
    for BHP<G, NUM_WINDOWS, WINDOW_SIZE>
{
    type Input = bool;
    type Output = G;

    /// Returns the BHP hash of the given input as an affine group element.
    ///
    /// This uncompressed variant of the BHP hash function is provided to support
    /// the BHP commitment scheme, as it is typically not used by applications.
    fn hash_uncompressed(&self, input: &[Self::Input]) -> Result<Self::Output> {
        // Ensure the input size is at least the window size.
        if input.len() <= WINDOW_SIZE * BHP_CHUNK_SIZE {
            bail!("Inputs to this BHP variant must be greater than {} bits", WINDOW_SIZE * BHP_CHUNK_SIZE)
        }

        // Ensure the input size is within the parameter size,
        if input.len() > NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE {
            bail!(
                "Invalid input size for Pedersen: expected <= {}, found {}",
                NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE,
                input.len()
            )
        }

        // Pad the input to a multiple of `BHP_CHUNK_SIZE` for hashing.
        let mut input = input.to_vec();
        if input.len() % BHP_CHUNK_SIZE != 0 {
            let padding = BHP_CHUNK_SIZE - (input.len() % BHP_CHUNK_SIZE);
            input.resize(input.len() + padding, false);
            assert_eq!(input.len() % BHP_CHUNK_SIZE, 0);
        }

        // Compute sum of h_i^{sum of (1-2*c_{i,j,2})*(1+c_{i,j,0}+2*c_{i,j,1})*2^{4*(j-1)} for all j in segment}
        // for all i. Described in section 5.4.1.7 in the Zcash protocol specification.
        //
        // Note: `.zip()` is used here (as opposed to `.zip_eq()`) as the input can be less than
        // `NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE` in length, which is the parameter size here.
        Ok(input
            .chunks(WINDOW_SIZE * BHP_CHUNK_SIZE)
            .zip(&self.bases_lookup)
            .flat_map(|(bits, bases)| {
                bits.chunks(BHP_CHUNK_SIZE).zip(bases).map(|(chunk_bits, base)| {
                    base[(chunk_bits[0] as usize) | (chunk_bits[1] as usize) << 1 | (chunk_bits[2] as usize) << 2]
                })
            })
            .sum::<G::Projective>()
            .to_affine())
    }
}
