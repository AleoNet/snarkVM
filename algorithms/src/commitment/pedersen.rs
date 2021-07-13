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

use crate::{
    commitment::PedersenCommitmentParameters,
    errors::CommitmentError,
    traits::{CommitmentScheme, CRH},
};
use snarkvm_curves::ProjectiveCurve;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::BitIteratorLE;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PedersenCommitment<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    pub parameters: PedersenCommitmentParameters<G, NUM_WINDOWS, WINDOW_SIZE>,
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CommitmentScheme
    for PedersenCommitment<G, NUM_WINDOWS, WINDOW_SIZE>
{
    type Output = G;
    type Parameters = PedersenCommitmentParameters<G, NUM_WINDOWS, WINDOW_SIZE>;
    type Randomness = G::ScalarField;

    fn setup(message: &str) -> Self {
        PedersenCommitmentParameters::setup(message).into()
    }

    fn commit(&self, input: &[u8], randomness: &Self::Randomness) -> Result<Self::Output, CommitmentError> {
        // If the input is too long, return an error.
        if input.len() > WINDOW_SIZE * NUM_WINDOWS {
            return Err(CommitmentError::IncorrectInputLength(
                input.len(),
                WINDOW_SIZE,
                NUM_WINDOWS,
            ));
        }

        let mut output = self.parameters.crh.hash(&input)?;

        // Compute h^r.
        let scalar_bits = BitIteratorLE::new(randomness.to_repr());
        for (bit, power) in scalar_bits.into_iter().zip(&self.parameters.random_base) {
            if bit {
                output += power
            }
        }

        Ok(output)
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.parameters
    }
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    From<PedersenCommitmentParameters<G, NUM_WINDOWS, WINDOW_SIZE>>
    for PedersenCommitment<G, NUM_WINDOWS, WINDOW_SIZE>
{
    fn from(parameters: PedersenCommitmentParameters<G, NUM_WINDOWS, WINDOW_SIZE>) -> Self {
        Self { parameters }
    }
}
