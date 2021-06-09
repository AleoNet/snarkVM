// Copyright (C) 2019-2021 Aleo Systems Inc.
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

pub use crate::crh::pedersen_parameters::PedersenSize;

use crate::{
    crh::PedersenCRHParameters,
    errors::CRHError,
    traits::{CRHParameters, CRH},
};
use bitvec::{order::Lsb0, view::BitView};
use snarkvm_curves::Group;
use snarkvm_fields::{ConstraintFieldError, Field, ToConstraintField};

use rand::Rng;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PedersenCRH<G: Group, S: PedersenSize> {
    pub parameters: PedersenCRHParameters<G, S>,
}

impl<G: Group, S: PedersenSize> CRH for PedersenCRH<G, S> {
    type Output = G;
    type Parameters = PedersenCRHParameters<G, S>;

    const INPUT_SIZE_BITS: usize = S::WINDOW_SIZE * S::NUM_WINDOWS;

    fn setup<R: Rng>(rng: &mut R) -> Self {
        Self {
            parameters: PedersenCRHParameters::setup(rng),
        }
    }

    fn hash(&self, input: &[u8]) -> Result<Self::Output, CRHError> {
        if (input.len() * 8) > S::WINDOW_SIZE * S::NUM_WINDOWS {
            return Err(CRHError::IncorrectInputLength(
                input.len(),
                S::WINDOW_SIZE,
                S::NUM_WINDOWS,
            ));
        }

        // Pad the input if it is not the current length.
        let mut input = input;
        let mut padded_input = vec![];
        if (input.len() * 8) < S::WINDOW_SIZE * S::NUM_WINDOWS {
            padded_input.extend_from_slice(input);
            padded_input.resize((S::WINDOW_SIZE * S::NUM_WINDOWS) / 8, 0u8);
            input = padded_input.as_slice();
        }

        if self.parameters.bases.len() != S::NUM_WINDOWS {
            return Err(CRHError::IncorrectParameterSize(
                self.parameters.bases[0].len(),
                self.parameters.bases.len(),
                S::WINDOW_SIZE,
                S::NUM_WINDOWS,
            ));
        }

        // Compute sum of h_i^{m_i} for all i.
        let bits = input.view_bits::<Lsb0>();
        let result = bits
            .chunks(S::WINDOW_SIZE)
            .zip(&self.parameters.bases)
            .map(|(bits, powers)| {
                let mut encoded = G::zero();
                for (bit, base) in bits.iter().zip(powers.iter()) {
                    if *bit {
                        encoded += base;
                    }
                }
                encoded
            })
            .fold(G::zero(), |a, b| a + &b);

        Ok(result)
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.parameters
    }
}

impl<G: Group, S: PedersenSize> From<PedersenCRHParameters<G, S>> for PedersenCRH<G, S> {
    fn from(parameters: PedersenCRHParameters<G, S>) -> Self {
        Self { parameters }
    }
}

impl<F: Field, G: Group + ToConstraintField<F>, S: PedersenSize> ToConstraintField<F> for PedersenCRH<G, S> {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        self.parameters.to_field_elements()
    }
}
