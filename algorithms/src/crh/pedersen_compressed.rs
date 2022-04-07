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

use crate::{crh::PedersenCRH, CRHError, CRH};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};

use std::fmt::Debug;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PedersenCompressedCRH<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    crh: PedersenCRH<G, NUM_WINDOWS, WINDOW_SIZE>,
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CRH
    for PedersenCompressedCRH<G, NUM_WINDOWS, WINDOW_SIZE>
{
    type Output = <G::Affine as AffineCurve>::BaseField;
    type Parameters = PedersenCRH<G, NUM_WINDOWS, WINDOW_SIZE>;

    fn setup(message: &str) -> Self {
        Self { crh: PedersenCRH::setup(message) }
    }

    /// Returns the affine x-coordinate as the collision-resistant hash output.
    fn hash(&self, input: &[bool]) -> Result<Self::Output, CRHError> {
        Ok(self.crh.hash(input)?.to_x_coordinate())
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.crh
    }
}
