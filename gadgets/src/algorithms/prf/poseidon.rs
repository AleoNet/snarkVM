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

use crate::{algorithms::crypto_hash::PoseidonCryptoHashGadget, FpGadget, PRFGadget};
use snarkvm_algorithms::prf::PoseidonPRF;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use std::marker::PhantomData;

pub struct PoseidonPRFGadget<F: PrimeField, const RATE: usize>(PhantomData<F>);

impl<F: PrimeField, const RATE: usize> PRFGadget<PoseidonPRF<F, RATE>, F> for PoseidonPRFGadget<F, RATE> {
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
            buffer.resize((F::size_in_bits() + 7) / 8, 0u8);
            F::from_bytes_le(&buffer)?
        };

        // Allocate the input length as a field element.
        let input_length_gadget = FpGadget::<F>::Constant(input_length);

        // Construct the preimage.
        let mut preimage = vec![seed.clone()];
        preimage.push(input_length_gadget);
        preimage.extend_from_slice(input.as_slice());

        // Evaluate the preimage.
        PoseidonCryptoHashGadget::<F, RATE>::check_evaluation_gadget(
            cs.ns(|| "Check Poseidon PRF evaluation"),
            &preimage,
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        algorithms::prf::*,
        traits::{algorithms::PRFGadget, alloc::AllocGadget, eq::EqGadget},
    };
    use snarkvm_algorithms::{prf::PoseidonPRF, PRF};
    use snarkvm_curves::bls12_377::Fr;
    use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    #[test]
    fn test_prf() {
        let mut rng = ChaChaRng::seed_from_u64(1231275789u64);
        let mut cs = TestConstraintSystem::<Fr>::new();

        let seed = rng.gen();
        let input = vec![rng.gen()];
        let output = PoseidonPRF::<Fr, 4>::prf(&seed, &input);

        let seed_gadget =
            <PoseidonPRFGadget<Fr, 4> as PRFGadget<_, Fr>>::Seed::alloc(&mut cs.ns(|| "seed"), || Ok(seed)).unwrap();
        let input_gadget =
            <PoseidonPRFGadget<Fr, 4> as PRFGadget<_, Fr>>::Input::alloc(&mut cs.ns(|| "input"), || Ok(input)).unwrap();

        let expected_output_gadget =
            <PoseidonPRFGadget<Fr, 4> as PRFGadget<_, Fr>>::Output::alloc(&mut cs.ns(|| "output"), || Ok(output))
                .unwrap();
        let candidate_output_gadget =
            PoseidonPRFGadget::<Fr, 4>::check_evaluation_gadget(&mut cs.ns(|| "evaluate"), &seed_gadget, &input_gadget)
                .unwrap();

        candidate_output_gadget.enforce_equal(&mut cs, &expected_output_gadget).unwrap();

        if !cs.is_satisfied() {
            println!("which is unsatisfied: {:?}", cs.which_is_unsatisfied().unwrap());
        }
        assert!(cs.is_satisfied());
    }
}
