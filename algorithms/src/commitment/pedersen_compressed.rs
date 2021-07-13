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
    commitment::{PedersenCommitment, PedersenCommitmentParameters},
    errors::CommitmentError,
    traits::CommitmentScheme,
};
use snarkvm_curves::traits::{AffineCurve, Group};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PedersenCompressedCommitment<G: AffineCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    pub parameters: PedersenCommitmentParameters<G, NUM_WINDOWS, WINDOW_SIZE>,
}

impl<G: AffineCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CommitmentScheme
    for PedersenCompressedCommitment<G, NUM_WINDOWS, WINDOW_SIZE>
{
    type Output = G::BaseField;
    type Parameters = PedersenCommitmentParameters<G, NUM_WINDOWS, WINDOW_SIZE>;
    type Randomness = <G as Group>::ScalarField;

    fn setup(message: &str) -> Self {
        PedersenCommitmentParameters::setup(message).into()
    }

    /// Returns the affine x-coordinate as the commitment.
    fn commit(&self, input: &[u8], randomness: &Self::Randomness) -> Result<Self::Output, CommitmentError> {
        let commitment = PedersenCommitment::<G, NUM_WINDOWS, WINDOW_SIZE> {
            parameters: self.parameters.clone(),
        };

        let output = commitment.commit(input, randomness)?;
        debug_assert!(output.is_in_correct_subgroup_assuming_on_curve());

        Ok(output.to_x_coordinate())
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.parameters
    }
}

impl<G: AffineCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    From<PedersenCommitmentParameters<G, NUM_WINDOWS, WINDOW_SIZE>>
    for PedersenCompressedCommitment<G, NUM_WINDOWS, WINDOW_SIZE>
{
    fn from(parameters: PedersenCommitmentParameters<G, NUM_WINDOWS, WINDOW_SIZE>) -> Self {
        Self { parameters }
    }
}
