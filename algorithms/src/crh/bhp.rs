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

use std::{fmt::Debug, sync::Arc};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub const BHP_CHUNK_SIZE: usize = 3;
pub const BHP_LOOKUP_SIZE: usize = 2usize.pow(BHP_CHUNK_SIZE as u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BHPCRH<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    pub bases: Arc<Vec<Vec<G>>>,
    base_lookup: Vec<Vec<[G; BHP_LOOKUP_SIZE]>>,
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CRH
    for BHPCRH<G, NUM_WINDOWS, WINDOW_SIZE>
{
    type Output = <G::Affine as AffineCurve>::BaseField;
    type Parameters = Arc<Vec<Vec<G>>>;

    fn setup(message: &str) -> Self {
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
                let (generator, _, _) = hash_to_curve::<G::Affine>(&format!("{message} at {index}"));
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
            .collect::<Vec<Vec<G>>>();
        debug_assert_eq!(bases.len(), NUM_WINDOWS, "Incorrect number of windows ({:?}) for BHP", bases.len());
        bases.iter().for_each(|window| debug_assert_eq!(window.len(), WINDOW_SIZE));

        // Compute the base lookup.
        let base_lookup = crate::cfg_iter!(bases)
            .map(|x| {
                x.iter()
                    .map(|g| {
                        let mut lookup = [G::zero(); BHP_LOOKUP_SIZE];
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
            .collect::<Vec<Vec<[G; BHP_LOOKUP_SIZE]>>>();
        debug_assert_eq!(base_lookup.len(), NUM_WINDOWS);
        base_lookup.iter().for_each(|bases| debug_assert_eq!(bases.len(), WINDOW_SIZE));

        Self { bases: Arc::new(bases), base_lookup }
    }

    fn hash(&self, input: &[bool]) -> Result<Self::Output, CRHError> {
        Ok(self.hash_bits_inner(input)?.to_affine().to_x_coordinate())
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.bases
    }
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> BHPCRH<G, NUM_WINDOWS, WINDOW_SIZE> {
    pub(crate) fn hash_bits_inner(&self, input: &[bool]) -> Result<G, CRHError> {
        // Ensure the input size is within the parameter size,
        if input.len() > NUM_WINDOWS * WINDOW_SIZE * BHP_CHUNK_SIZE {
            return Err(CRHError::IncorrectInputLength(input.len(), WINDOW_SIZE, NUM_WINDOWS * BHP_CHUNK_SIZE));
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
            .zip(&self.base_lookup)
            .flat_map(|(bits, bases)| {
                bits.chunks(BHP_CHUNK_SIZE).zip(bases).map(|(chunk_bits, base)| {
                    base[(chunk_bits[0] as usize) | (chunk_bits[1] as usize) << 1 | (chunk_bits[2] as usize) << 2]
                })
            })
            .sum())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::edwards_bls12::EdwardsProjective;

    const NUM_WINDOWS: usize = 8;
    const WINDOW_SIZE: usize = 32;

    #[test]
    fn test_bhp_sanity_check() {
        let crh = <BHPCRH<EdwardsProjective, NUM_WINDOWS, WINDOW_SIZE> as CRH>::setup("test_bowe_pedersen");
        let input = vec![127u8; 32];

        let output = crh.hash_bytes(&input).unwrap();
        assert_eq!(
            &*output.to_string(),
            "2591648422993904809826711498838675948697848925001720514073745852367402669969"
        );
    }
}
