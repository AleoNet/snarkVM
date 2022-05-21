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

use crate::{crypto_hash::hash_to_curve, CRHError, CRH};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::BigInteger;

use std::borrow::Cow;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SinsemillaParameters<G: ProjectiveCurve> {
    q: G,
    p_lookups: Vec<G>,
}

/// SinsemillaCRH is a collision-resistant hash function that takes a fixed-length input.
/// The Sinsemilla hash function does *not* behave like a random oracle, see Poseidon for one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SinsemillaCRH<G: ProjectiveCurve, const WINDOW_SIZE: usize, const NUM_WINDOWS: usize>(
    SinsemillaParameters<G>,
);

impl<G: ProjectiveCurve, const WINDOW_SIZE: usize, const NUM_WINDOWS: usize> CRH
    for SinsemillaCRH<G, WINDOW_SIZE, NUM_WINDOWS>
{
    type Output = <G::Affine as AffineCurve>::BaseField;
    type Parameters = SinsemillaParameters<G>;

    /// Initializes a new instance of Sinsemilla with the given setup message.
    fn setup(message: &str) -> Self {
        // Calculate the maximum window size.
        let mut maximum_window_size = 0;
        let mut range = <G::ScalarField as PrimeField>::BigInteger::from(2_u64);
        while range < G::ScalarField::modulus_minus_one_div_two() {
            // range < (p-1)/2
            range.muln(1);
            maximum_window_size += 1;
        }
        assert!(WINDOW_SIZE <= maximum_window_size, "The maximum Sinsemilla window size is {maximum_window_size}");

        // Compute Q
        let (q, _, _) = hash_to_curve::<G::Affine>(message);
        let q = q.to_projective();

        // Compute P[0..2^WINDOW_SIZE-1]
        let table_size = 2usize.pow(WINDOW_SIZE as u32);
        let mut p_lookups: Vec<G> = Vec::with_capacity(table_size);
        for i in 0..table_size {
            let (p, _, _) = hash_to_curve::<G::Affine>(&format!("{:?}", (i as u32).to_le_bytes()));
            p_lookups.push(p.to_projective());
        }

        Self(SinsemillaParameters { q, p_lookups })
    }

    fn hash(&self, input: &[bool]) -> Result<Self::Output, CRHError> {
        Ok(self.hash_bits_inner(input)?.to_affine().to_x_coordinate())
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.0
    }
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    SinsemillaCRH<G, NUM_WINDOWS, WINDOW_SIZE>
{
    pub(crate) fn hash_bits_inner(&self, input: &[bool]) -> Result<G, CRHError> {
        // Ensure the input size is within the size bounds.
        let mut input = Cow::Borrowed(input);
        match input.len() <= NUM_WINDOWS * WINDOW_SIZE {
            // Pad the input if it is under the required parameter size.
            true => input.to_mut().resize(WINDOW_SIZE * NUM_WINDOWS, false),
            // Ensure the input size is within the parameter size.
            false => return Err(CRHError::IncorrectInputLength(input.len(), WINDOW_SIZE, NUM_WINDOWS)),
        }

        Ok(input.chunks(WINDOW_SIZE).fold(self.0.q.clone(), |acc, bits| {
            let mut i = 0u16;
            bits.iter().for_each(|bit| {
                i <<= 1;
                if *bit {
                    i |= 1u16;
                }
            });
            acc.double() + self.0.p_lookups[i as usize]
        }))
    }
}
