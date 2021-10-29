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

use crate::{crh::BHPCRH, hash_to_curve::hash_to_curve, CommitmentError, CommitmentScheme, CRH};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::{ConstraintFieldError, Field, PrimeField, ToConstraintField};
use snarkvm_utilities::{BitIteratorLE, FromBytes, ToBytes};

use std::{
    fmt::Debug,
    io::{Read, Result as IoResult, Write},
    sync::Arc,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BHPCommitment<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    pub bhp_crh: BHPCRH<G, NUM_WINDOWS, WINDOW_SIZE>,
    pub random_base: Vec<G>,
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CommitmentScheme
    for BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE>
{
    type Output = <G::Affine as AffineCurve>::BaseField;
    type Parameters = (Arc<Vec<Vec<G>>>, Vec<G>);
    type Randomness = G::ScalarField;

    fn setup(message: &str) -> Self {
        // First, compute the bases.
        let bhp = BHPCRH::<G, NUM_WINDOWS, WINDOW_SIZE>::setup(message).into();

        // Next, compute the random base.
        let random_base_message = format!("{} for random base", message);
        let (generator, _, _) = hash_to_curve::<G::Affine>(&random_base_message);
        let mut base = generator.into_projective();
        let mut random_base = Vec::with_capacity(WINDOW_SIZE);
        for _ in 0..WINDOW_SIZE {
            random_base.push(base);
            base.double_in_place();
        }

        Self {
            bhp_crh: bhp,
            random_base,
        }
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

        // Convert input bytes to bits.
        let bits = input
            .iter()
            .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
            .collect::<Vec<bool>>();

        let mut output = self.bhp_crh.hash_bits_inner(&bits)?;

        // Compute h^r.
        let scalar_bits = BitIteratorLE::new(randomness.to_repr());
        for (bit, power) in scalar_bits.into_iter().zip(&self.random_base) {
            if bit {
                output += power
            }
        }

        let affine = output.into_affine();
        debug_assert!(affine.is_in_correct_subgroup_assuming_on_curve());
        Ok(affine.to_x_coordinate())
    }

    fn parameters(&self) -> Self::Parameters {
        (self.bhp_crh.bases.clone(), self.random_base.clone())
    }
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> From<(Arc<Vec<Vec<G>>>, Vec<G>)>
    for BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE>
{
    fn from((bases, random_base): (Arc<Vec<Vec<G>>>, Vec<G>)) -> Self {
        Self {
            bhp_crh: bases.into(),
            random_base,
        }
    }
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> ToBytes
    for BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE>
{
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.bhp_crh.write_le(&mut writer)?;

        (self.random_base.len() as u32).write_le(&mut writer)?;
        for g in &self.random_base {
            g.write_le(&mut writer)?;
        }

        Ok(())
    }
}

impl<G: ProjectiveCurve, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> FromBytes
    for BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE>
{
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let bhp = BHPCRH::read_le(&mut reader)?;

        let random_base_len: u32 = FromBytes::read_le(&mut reader)?;
        let mut random_base = Vec::with_capacity(random_base_len as usize);
        for _ in 0..random_base_len {
            let g: G = FromBytes::read_le(&mut reader)?;
            random_base.push(g);
        }

        Ok(Self {
            bhp_crh: bhp,
            random_base,
        })
    }
}

impl<F: Field, G: ProjectiveCurve + ToConstraintField<F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    ToConstraintField<F> for BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE>
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        Ok(Vec::new())
    }
}
