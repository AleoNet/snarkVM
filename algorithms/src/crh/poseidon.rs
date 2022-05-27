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

use crate::{crypto_hash::Poseidon, CRHError, CRH};
use snarkvm_fields::{FieldParameters, PoseidonParameters, PrimeField, ToConstraintField};

use std::{borrow::Cow, fmt::Debug, sync::Arc};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoseidonCRH<F: PrimeField, const INPUT_SIZE_FE: usize>(Poseidon<F, 4>);

impl<F: PrimeField, const INPUT_SIZE_FE: usize> CRH for PoseidonCRH<F, INPUT_SIZE_FE> {
    type Output = F;
    type Parameters = Arc<PoseidonParameters<F, 4, 1>>;

    fn setup(_message: &str) -> Self {
        Self(Poseidon::<F, 4>::setup())
    }

    fn hash(&self, input: &[bool]) -> Result<Self::Output, CRHError> {
        // Pad the input if necessary.
        let input = {
            let input_size_bits: usize = INPUT_SIZE_FE * <F as PrimeField>::Parameters::CAPACITY as usize;

            assert!(input.len() <= input_size_bits, "PoseidonCRH input bits exceeds supported input size");

            let mut input = Cow::Borrowed(input);
            if input.len() < input_size_bits {
                input.to_mut().resize(input_size_bits, false);
            }
            input
        };

        Ok(self.0.evaluate(&input.to_field_elements()?))
    }

    fn parameters(&self) -> &Self::Parameters {
        self.0.parameters()
    }
}
