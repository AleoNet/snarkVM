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

use crate::{commitment::BHPCommitmentScheme, CommitmentError, CommitmentScheme};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::{ConstraintFieldError, Field, ToConstraintField};
use snarkvm_utilities::{FromBytes, ToBytes};

use std::{
    fmt::Debug,
    io::{Read, Result as IoResult, Write},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BHPCompressedCommitmentScheme<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    pub bhp: BHPCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>,
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CommitmentScheme
    for BHPCompressedCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>
{
    type Output = <G::Affine as AffineCurve>::BaseField;
    type Parameters = BHPCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>;
    type Randomness = G::ScalarField;

    fn setup(message: &str) -> Self {
        BHPCommitmentScheme::<G, NUM_WINDOWS, WINDOW_SIZE>::setup(message).into()
    }

    fn commit(&self, input: &[u8], randomness: &Self::Randomness) -> Result<Self::Output, CommitmentError> {
        let affine = self.bhp.commit(input, randomness)?;
        debug_assert!(affine.is_in_correct_subgroup_assuming_on_curve());
        Ok(affine.to_x_coordinate())
    }

    fn parameters(&self) -> Self::Parameters {
        self.bhp.clone()
    }
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    From<BHPCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>>
    for BHPCompressedCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>
{
    fn from(bhp: BHPCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>) -> Self {
        Self { bhp }
    }
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> From<(Vec<Vec<G>>, Vec<G>)>
    for BHPCompressedCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>
{
    fn from((bases, random_base): (Vec<Vec<G>>, Vec<G>)) -> Self {
        BHPCommitmentScheme::from((bases, random_base)).into()
    }
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> ToBytes
    for BHPCompressedCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>
{
    fn write_le<W: Write>(&self, writer: W) -> IoResult<()> {
        self.bhp.write_le(writer)
    }
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> FromBytes
    for BHPCompressedCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>
{
    #[inline]
    fn read_le<R: Read>(reader: R) -> IoResult<Self> {
        Ok(BHPCommitmentScheme::read_le(reader)?.into())
    }
}

impl<F: Field, G: ProjectiveCurve + ToConstraintField<F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    ToConstraintField<F> for BHPCompressedCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        self.bhp.to_field_elements()
    }
}
