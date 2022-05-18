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

use crate::{crypto_hash::Poseidon, PRF};
use snarkvm_fields::PrimeField;

use std::marker::PhantomData;

#[derive(Clone)]
pub struct PoseidonPRF<F: PrimeField, const RATE: usize>(PhantomData<F>);

impl<F: PrimeField, const RATE: usize> PRF for PoseidonPRF<F, RATE> {
    type Input = Vec<F>;
    type Output = F;
    type Seed = F;

    fn prf(seed: &Self::Seed, input: &Self::Input) -> Self::Output {
        // Construct the preimage.
        let mut preimage = vec![*seed];
        preimage.push(F::from(input.len() as u128)); // Input length
        preimage.extend_from_slice(input);

        // Evaluate the preimage.
        Poseidon::<F, RATE>::setup().evaluate(&preimage)
    }
}
