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

use itertools::Itertools;
use std::{borrow::Cow, fmt::Debug};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PedersenCRH<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    pub bases: Vec<Vec<G>>,
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CRH
    for PedersenCRH<G, NUM_WINDOWS, WINDOW_SIZE>
{
    type Output = G::Affine;
    type Parameters = Vec<Vec<G>>;

    fn setup(message: &str) -> Self {
        let bases = (0..NUM_WINDOWS)
            .map(|index| {
                // Construct an indexed message to attempt to sample a base.
                let (generator, _, _) = hash_to_curve::<G::Affine>(&format!("{message} at {index}"));
                let mut base = generator.to_projective();
                let mut powers = Vec::with_capacity(WINDOW_SIZE);
                for _ in 0..WINDOW_SIZE {
                    powers.push(base);
                    base.double_in_place();
                }
                powers
            })
            .collect();

        Self { bases }
    }

    fn hash(&self, input: &[bool]) -> Result<Self::Output, CRHError> {
        let mut input = Cow::Borrowed(input);
        match input.len() <= WINDOW_SIZE * NUM_WINDOWS {
            // Pad the input if it is under the required parameter size.
            true => input.to_mut().resize(WINDOW_SIZE * NUM_WINDOWS, false),
            // Ensure the input size is within the parameter size,
            false => return Err(CRHError::IncorrectInputLength(input.len(), WINDOW_SIZE, NUM_WINDOWS)),
        }

        // Compute sum of h_i^{m_i} for all i.
        Ok(input
            .chunks(WINDOW_SIZE)
            .zip_eq(&self.bases)
            .flat_map(|(bits, powers)| {
                bits.iter().zip_eq(powers).flat_map(|(bit, base)| match bit {
                    true => Some(*base),
                    false => None,
                })
            })
            .sum::<G>()
            .to_affine())
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.bases
    }
}
