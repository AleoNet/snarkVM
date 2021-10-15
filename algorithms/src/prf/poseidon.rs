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
    crypto_hash::{PoseidonCryptoHash, PoseidonDefaultParametersField},
    errors::PRFError,
    traits::{CryptoHash, PRF},
};
use snarkvm_fields::PrimeField;

use std::marker::PhantomData;

#[derive(Clone)]
pub struct PoseidonPRF<
    F: PrimeField + PoseidonDefaultParametersField,
    const RATE: usize,
    const OPTIMIZED_FOR_WEIGHTS: bool,
>(PhantomData<F>);

impl<F: PrimeField + PoseidonDefaultParametersField, const RATE: usize, const OPTIMIZED_FOR_WEIGHTS: bool> PRF
    for PoseidonPRF<F, RATE, OPTIMIZED_FOR_WEIGHTS>
{
    type Input = Vec<F>;
    type Output = F;
    type Seed = F;

    fn evaluate(seed: &Self::Seed, input: &Self::Input) -> Result<Self::Output, PRFError> {
        let timer = start_timer!(|| "PoseidonPRF::evaluate");

        // Construct the input length as a field element.
        let input_length = {
            let mut buffer = input.len().to_le_bytes().to_vec();
            buffer.resize(F::size_in_bits() + 7 / 8, 0u8);
            F::from_bytes_le(&buffer)?
        };

        // Construct the preimage.
        let mut preimage = vec![*seed];
        preimage.push(input_length);
        preimage.extend_from_slice(input);

        // Evaluate the preimage.
        let output = PoseidonCryptoHash::<F, RATE, OPTIMIZED_FOR_WEIGHTS>::setup().evaluate(preimage.as_slice());

        end_timer!(timer);
        Ok(output)
    }
}
