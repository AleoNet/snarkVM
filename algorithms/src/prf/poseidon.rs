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
    type Input = F;
    type Output = F;
    type Seed = F;

    fn evaluate(seed: &Self::Seed, input: &Self::Input) -> Result<Self::Output, PRFError> {
        let eval_time = start_timer!(|| "PoseidonPRF::evaluate");
        let result = PoseidonCryptoHash::<F, RATE, OPTIMIZED_FOR_WEIGHTS>::evaluate(&[*seed, *input])?;
        end_timer!(eval_time);
        Ok(result)
    }
}
