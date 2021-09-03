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
    crh::{BoweHopwoodPedersenCRH, BoweHopwoodPedersenCRHParameters, PedersenCRH, PedersenCRHParameters},
    errors::CRHError,
    traits::CRH,
};
use snarkvm_curves::{AffineCurve, Group, ProjectiveCurve};
use snarkvm_fields::{ConstraintFieldError, Field, ToConstraintField};

use rand::Rng;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoweHopwoodPedersenCompressedCRH<
    G: Group + ProjectiveCurve,
    const NUM_WINDOWS: usize,
    const WINDOW_SIZE: usize,
> {
    pub parameters: PedersenCRHParameters<G, NUM_WINDOWS, WINDOW_SIZE>,
    pub bowe_hopwood_parameters: BoweHopwoodPedersenCRHParameters<G>,
}

impl<G: Group + ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CRH
    for BoweHopwoodPedersenCompressedCRH<G, NUM_WINDOWS, WINDOW_SIZE>
{
    type Output = <G::Affine as AffineCurve>::BaseField;
    type Parameters = PedersenCRHParameters<G, NUM_WINDOWS, WINDOW_SIZE>;

    const INPUT_SIZE_BITS: usize = PedersenCRH::<G, NUM_WINDOWS, WINDOW_SIZE>::INPUT_SIZE_BITS;

    fn setup<R: Rng>(rng: &mut R) -> Self {
        let BoweHopwoodPedersenCRH {
            parameters,
            bowe_hopwood_parameters,
        } = BoweHopwoodPedersenCRH::<G, NUM_WINDOWS, WINDOW_SIZE>::setup(rng);

        Self {
            parameters,
            bowe_hopwood_parameters,
        }
    }

    fn hash(&self, input: &[u8]) -> Result<Self::Output, CRHError> {
        let crh = BoweHopwoodPedersenCRH::<G, NUM_WINDOWS, WINDOW_SIZE> {
            parameters: self.parameters.clone(),
            bowe_hopwood_parameters: self.bowe_hopwood_parameters.clone(),
        };

        let output = crh.hash(input)?;
        let affine = output.into_affine();
        debug_assert!(affine.is_in_correct_subgroup_assuming_on_curve());
        Ok(affine.to_x_coordinate())
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.parameters
    }
}

impl<G: Group + ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    From<PedersenCRHParameters<G, NUM_WINDOWS, WINDOW_SIZE>>
    for BoweHopwoodPedersenCompressedCRH<G, NUM_WINDOWS, WINDOW_SIZE>
{
    fn from(parameters: PedersenCRHParameters<G, NUM_WINDOWS, WINDOW_SIZE>) -> Self {
        Self {
            bowe_hopwood_parameters: BoweHopwoodPedersenCRHParameters::setup(&parameters),
            parameters,
        }
    }
}

impl<
        F: Field,
        G: Group + ProjectiveCurve + ToConstraintField<F>,
        const NUM_WINDOWS: usize,
        const WINDOW_SIZE: usize,
    > ToConstraintField<F> for BoweHopwoodPedersenCompressedCRH<G, NUM_WINDOWS, WINDOW_SIZE>
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        self.parameters.to_field_elements()
    }
}
