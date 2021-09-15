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
    algorithms::crypto_hash::PoseidonCryptoHashGadget,
    traits::alloc::AllocGadget,
    CryptoHashGadget,
    FpGadget,
    PRFGadget,
};
use snarkvm_algorithms::{crypto_hash::PoseidonDefaultParametersField, prf::PoseidonPRF};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use std::marker::PhantomData;

pub struct PoseidonPRFGadget<
    F: PrimeField + PoseidonDefaultParametersField,
    const RATE: usize,
    const OPTIMIZED_FOR_WEIGHTS: bool,
>(PhantomData<F>);

impl<F: PrimeField + PoseidonDefaultParametersField, const RATE: usize, const OPTIMIZED_FOR_WEIGHTS: bool>
    PRFGadget<PoseidonPRF<F, RATE, OPTIMIZED_FOR_WEIGHTS>, F> for PoseidonPRFGadget<F, RATE, OPTIMIZED_FOR_WEIGHTS>
{
    type Input = Vec<FpGadget<F>>;
    type Output = FpGadget<F>;
    type Seed = FpGadget<F>;

    fn check_evaluation_gadget<CS: ConstraintSystem<F>>(
        mut cs: CS,
        seed: &Self::Seed,
        input: &Self::Input,
    ) -> Result<Self::Output, SynthesisError> {
        // Construct the input length as a field element.
        let input_length = {
            let mut buffer = input.len().to_le_bytes().to_vec();
            buffer.resize(F::size_in_bits() + 7 / 8, 0u8);
            F::from_bytes_le(&buffer)?
        };

        // Allocate the input length as a field element.
        let input_length_gadget = FpGadget::<F>::alloc(cs.ns(|| "Allocate input length"), || Ok(&input_length))?;

        // Construct the preimage.
        let mut preimage = vec![seed.clone()];
        preimage.push(input_length_gadget);
        preimage.extend_from_slice(input.as_slice());

        // Evaluate the preimage.
        PoseidonCryptoHashGadget::<F, RATE, OPTIMIZED_FOR_WEIGHTS>::check_evaluation_gadget(
            cs.ns(|| "Check Poseidon PRF evaluation"),
            &preimage,
        )
    }
}
