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

use crate::{hash_to_curve::hash_to_curve, CRHError, CRH};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::{ConstraintFieldError, Field, ToConstraintField};

use itertools::Itertools;
use std::{borrow::Cow, fmt::Debug};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PedersenCRH<G: ProjectiveCurve, const INPUT_SIZE: usize> {
    pub bases: Vec<Vec<G>>,
}

impl<G: ProjectiveCurve, const INPUT_SIZE: usize> CRH for PedersenCRH<G, INPUT_SIZE> {
    type Output = G::Affine;
    type Parameters = Vec<Vec<G>>;

    fn setup(message: &str) -> Self {
        let (num_windows, window_size) = Self::window();

        let bases = (0..num_windows)
            .map(|index| {
                // Construct an indexed message to attempt to sample a base.
                let (generator, _, _) = hash_to_curve::<G::Affine>(&format!("{message} at {index}"));
                let mut base = generator.into_projective();
                let mut powers = Vec::with_capacity(window_size);
                for _ in 0..window_size {
                    powers.push(base);
                    base.double_in_place();
                }
                powers
            })
            .collect();

        Self { bases }
    }

    fn hash(&self, input: &[bool]) -> Result<Self::Output, CRHError> {
        let (num_windows, window_size) = Self::window();

        let mut input = Cow::Borrowed(input);
        match input.len() <= window_size * num_windows {
            // Pad the input if it is under the required parameter size.
            true => input.to_mut().resize(window_size * num_windows, false),
            // Ensure the input size is within the parameter size,
            false => return Err(CRHError::IncorrectInputLength(input.len(), window_size, num_windows)),
        }

        // Compute sum of h_i^{m_i} for all i.
        Ok(input
            .chunks(window_size)
            .zip_eq(&self.bases)
            .flat_map(|(bits, powers)| {
                bits.iter().zip_eq(powers).flat_map(|(bit, base)| match bit {
                    true => Some(*base),
                    false => None,
                })
            })
            .sum::<G>()
            .into_affine())
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.bases
    }

    fn window() -> (usize, usize) {
        fn div_up(a: usize, b: usize) -> usize {
            (a + (b - 1)) / b
        }

        const MAXIMUM_ITERATIONS: usize = 64;
        const NUM_WINDOWS_GROWTH_FACTOR: usize = 2;

        let mut num_windows: usize = 2;
        let window_size: usize = div_up(INPUT_SIZE, num_windows);
        let mut remainder = num_windows.saturating_mul(window_size) % INPUT_SIZE;

        let mut final_num_windows: usize = num_windows;
        let mut final_window_size: usize = window_size;

        let mut iteration = 0;

        while remainder != 0 && num_windows < INPUT_SIZE && iteration < MAXIMUM_ITERATIONS {
            let new_num_windows = num_windows.saturating_add(NUM_WINDOWS_GROWTH_FACTOR);
            let new_window_size = div_up(INPUT_SIZE, new_num_windows);
            let new_remainder = new_num_windows.saturating_mul(new_window_size) % INPUT_SIZE;

            if new_remainder <= remainder {
                final_num_windows = new_num_windows;
                final_window_size = new_window_size;
                remainder = new_remainder;
            }

            num_windows = new_num_windows;
            iteration += 1;
        }

        (final_num_windows, final_window_size)
    }
}

impl<F: Field, G: ProjectiveCurve + ToConstraintField<F>, const INPUT_SIZE: usize> ToConstraintField<F>
    for PedersenCRH<G, INPUT_SIZE>
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        Ok(Vec::new())
    }
}
