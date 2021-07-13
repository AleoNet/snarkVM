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

use snarkvm_curves::ProjectiveCurve;
use snarkvm_fields::{ConstraintFieldError, Field, ToConstraintField};
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::Rng;
use std::io::{Read, Result as IoResult, Write};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "G: ProjectiveCurve"),
    Debug(bound = "G: ProjectiveCurve"),
    PartialEq(bound = "G: ProjectiveCurve"),
    Eq(bound = "G: ProjectiveCurve")
)]
pub struct GroupEncryptionParameters<G: ProjectiveCurve> {
    pub generator_powers: Vec<G>,
    pub salt: [u8; 32],
}

impl<G: ProjectiveCurve> GroupEncryptionParameters<G> {
    pub fn setup<R: Rng>(rng: &mut R, private_key_size_in_bits: usize) -> Self {
        // Round to the closest multiple of 64 to factor bit and byte encoding differences.
        assert!(private_key_size_in_bits < usize::MAX - 63);
        let num_powers = (private_key_size_in_bits + 63) & !63usize;
        Self {
            generator_powers: Self::generator(num_powers, rng),
            salt: rng.gen(),
        }
    }

    fn generator<R: Rng>(num_powers: usize, rng: &mut R) -> Vec<G> {
        let mut generator_powers = Vec::with_capacity(num_powers);
        let mut generator = G::rand(rng);
        for _ in 0..num_powers {
            generator_powers.push(generator);
            generator.double_in_place();
        }
        generator_powers
    }
}

impl<G: ProjectiveCurve> ToBytes for GroupEncryptionParameters<G> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.generator_powers.len() as u32).write_le(&mut writer)?;
        for g in &self.generator_powers {
            g.write_le(&mut writer)?;
        }
        self.salt.write_le(&mut writer)
    }
}

impl<G: ProjectiveCurve> FromBytes for GroupEncryptionParameters<G> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let generator_powers_length: u32 = FromBytes::read_le(&mut reader)?;
        let mut generator_powers = Vec::with_capacity(generator_powers_length as usize);
        for _ in 0..generator_powers_length {
            let g: G = FromBytes::read_le(&mut reader)?;
            generator_powers.push(g);
        }

        let salt: [u8; 32] = FromBytes::read_le(&mut reader)?;

        Ok(Self { generator_powers, salt })
    }
}

impl<F: Field, G: ProjectiveCurve + ToConstraintField<F>> ToConstraintField<F> for GroupEncryptionParameters<G> {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        Ok(Vec::new())
    }
}
