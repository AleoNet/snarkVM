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

use crate::traits::crh::CRHParameters;
use snarkvm_curves::Group;
use snarkvm_fields::{ConstraintFieldError, Field, ToConstraintField};
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::Rng;
use std::{
    fmt::Debug,
    io::{Read, Result as IoResult, Write},
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PedersenCRHParameters<G: Group, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> {
    pub bases: Vec<Vec<G>>,
}

impl<G: Group, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> CRHParameters
    for PedersenCRHParameters<G, NUM_WINDOWS, WINDOW_SIZE>
{
    fn setup<R: Rng>(rng: &mut R) -> Self {
        Self {
            bases: (0..NUM_WINDOWS).map(|_| Self::base(WINDOW_SIZE, rng)).collect(),
        }
    }
}

impl<G: Group, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> PedersenCRHParameters<G, NUM_WINDOWS, WINDOW_SIZE> {
    pub fn from(bases: Vec<Vec<G>>) -> Self {
        Self { bases }
    }

    fn base<R: Rng>(num_powers: usize, rng: &mut R) -> Vec<G> {
        let mut powers = Vec::with_capacity(num_powers);
        let mut base = G::rand(rng);
        for _ in 0..num_powers {
            powers.push(base);
            base.double_in_place();
        }
        powers
    }
}

impl<G: Group, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> ToBytes
    for PedersenCRHParameters<G, NUM_WINDOWS, WINDOW_SIZE>
{
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.bases.len() as u32).write_le(&mut writer)?;
        for base in &self.bases {
            (base.len() as u32).write_le(&mut writer)?;
            for g in base {
                g.write_le(&mut writer)?;
            }
        }
        Ok(())
    }
}

impl<G: Group, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> FromBytes
    for PedersenCRHParameters<G, NUM_WINDOWS, WINDOW_SIZE>
{
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let num_bases: u32 = FromBytes::read(&mut reader)?;
        let mut bases = Vec::with_capacity(num_bases as usize);

        for _ in 0..num_bases {
            let base_len: u32 = FromBytes::read(&mut reader)?;
            let mut base = Vec::with_capacity(base_len as usize);

            for _ in 0..base_len {
                let g: G = FromBytes::read(&mut reader)?;
                base.push(g);
            }
            bases.push(base);
        }

        Ok(Self { bases })
    }
}

impl<F: Field, G: Group + ToConstraintField<F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize> ToConstraintField<F>
    for PedersenCRHParameters<G, NUM_WINDOWS, WINDOW_SIZE>
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        Ok(Vec::new())
    }
}
