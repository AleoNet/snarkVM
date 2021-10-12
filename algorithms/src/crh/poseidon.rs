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
    crypto_hash::{PoseidonCryptoHash, PoseidonDefaultParametersField, PoseidonParameters},
    traits::{CryptoHash, CRH},
    CRHError,
};
use snarkvm_fields::{ConstraintFieldError, FieldParameters, PrimeField, ToConstraintField};
use snarkvm_utilities::{any::TypeId, FromBytes, ToBytes};

use std::{
    borrow::Cow,
    fmt::Debug,
    io::{Read, Result as IoResult, Write},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoseidonCRH<F: PrimeField + PoseidonDefaultParametersField, const INPUT_SIZE_FE: usize>(
    PoseidonParameters<F>,
);

impl<F: PrimeField + PoseidonDefaultParametersField, const INPUT_SIZE_FE: usize> CRH for PoseidonCRH<F, INPUT_SIZE_FE> {
    type Output = F;
    type Parameters = PoseidonParameters<F>;

    fn setup(_message: &str) -> Self {
        Self(F::get_default_poseidon_parameters(4, false).unwrap())
    }

    fn hash_bits(&self, input: &[bool]) -> Result<Self::Output, CRHError> {
        // Pad the input if necessary.
        let input = {
            let input_size_bits: usize = INPUT_SIZE_FE * <F as PrimeField>::Parameters::CAPACITY as usize;

            assert!(
                input.len() <= input_size_bits,
                "PoseidonCRH input bits exceeds supported input size"
            );

            let mut input = Cow::Borrowed(input);
            if input.len() < input_size_bits {
                input.to_mut().resize(input_size_bits, false);
            }
            input
        };

        Ok(PoseidonCryptoHash::<F, 4, false>::evaluate(
            &input.to_field_elements()?,
        )?)
    }

    fn hash_field_elements<F2: PrimeField>(&self, input: &[F2]) -> Result<Self::Output, CRHError> {
        if TypeId::of::<F2>() == TypeId::of::<F>() {
            let mut dest = vec![];
            for item in input.iter() {
                dest.push(F::from_bytes_le(&item.to_bytes_le()?)?)
            }

            // Pad the input if necessary.
            let dest = {
                assert!(dest.len() <= INPUT_SIZE_FE);

                let mut dest = Cow::Borrowed(&dest);
                if dest.len() < INPUT_SIZE_FE {
                    dest.to_mut().resize(INPUT_SIZE_FE, F::zero());
                }
                dest
            };

            Ok(PoseidonCryptoHash::<F, 4, false>::evaluate(&dest)?)
        } else {
            unimplemented!()
        }
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.0
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField, const INPUT_SIZE_FE: usize> From<PoseidonParameters<F>>
    for PoseidonCRH<F, INPUT_SIZE_FE>
{
    fn from(parameters: PoseidonParameters<F>) -> Self {
        Self(parameters)
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField, const INPUT_SIZE_FE: usize> FromBytes
    for PoseidonCRH<F, INPUT_SIZE_FE>
{
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let parameters: PoseidonParameters<F> = FromBytes::read_le(&mut reader)?;
        Ok(Self(parameters))
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField, const INPUT_SIZE_FE: usize> ToBytes
    for PoseidonCRH<F, INPUT_SIZE_FE>
{
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField> ToConstraintField<F> for PoseidonParameters<F> {
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        // do not write into field elements
        Ok(vec![])
    }
}
