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
    algorithms::commitment::{pedersen::*, PedersenCompressedCommitmentGadget},
    bits::Boolean,
    integers::uint::UInt8,
    traits::{
        alloc::AllocGadget,
        integers::Integer,
        CommitmentGadget,
        CompressedGroupGadget,
        ValueBalanceCommitmentGadget,
    },
};

use snarkvm_algorithms::commitment::PedersenCompressedCommitment;
use snarkvm_curves::{Group, ProjectiveCurve};
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use std::marker::PhantomData;

pub struct ValueBalanceCommitmentVerificationGadget<
    G: Group + ProjectiveCurve,
    F: Field,
    GG: CompressedGroupGadget<G, F>,
>(PhantomData<G>, PhantomData<GG>, PhantomData<F>);

impl<
    F: PrimeField,
    G: Group + ProjectiveCurve,
    GG: CompressedGroupGadget<G, F>,
    const NUM_WINDOWS: usize,
    const WINDOW_SIZE: usize,
> ValueBalanceCommitmentGadget<PedersenCompressedCommitment<G, NUM_WINDOWS, WINDOW_SIZE>, F, G>
    for ValueBalanceCommitmentVerificationGadget<G, F, GG>
{
    type CommitmentGadget = PedersenCompressedCommitmentGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>;
    type OutputGadget = GG;
    type RandomnessGadget = PedersenRandomnessGadget<G>;

    fn check_value_commitment_gadget<CS: ConstraintSystem<F>>(
        mut cs: CS,
        commitment_scheme: &Self::CommitmentGadget,
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError> {
        let default_randomness = Self::RandomnessGadget::alloc(&mut cs.ns(|| "default_randomness"), || {
            Ok(<G as Group>::ScalarField::default())
        })?;

        let output = commitment_scheme.pedersen.check_commitment_gadget(cs, input, &default_randomness)?;
        Ok(output)
    }

    fn check_value_balance_commitment_gadget<CS: ConstraintSystem<F>>(
        mut cs: CS,
        partial_bvk: &Self::OutputGadget,
        value_balance_comm: &Self::OutputGadget,
        is_negative: &Boolean,
        c: &Self::RandomnessGadget,
        affine_r: &Self::OutputGadget,
        recommit: &Self::OutputGadget,
    ) -> Result<(), SynthesisError> {
        // TODO (raychu86) make this circuit more efficient

        let negative_bvk = partial_bvk.add(cs.ns(|| "construct_negative_bvk"), value_balance_comm)?;
        let positive_bvk = partial_bvk.sub(cs.ns(|| "construct_positive_bvk"), value_balance_comm)?;

        let c_bits: Vec<_> = c.0.iter().flat_map(|byte| byte.to_bits_le()).collect();
        let zero = GG::zero(&mut cs.ns(|| "zero")).unwrap();

        let negative_result = negative_bvk.mul_bits(cs.ns(|| "mul_bits_negative"), &zero, c_bits.iter().cloned())?;
        let positive_result = positive_bvk.mul_bits(cs.ns(|| "mul_bits_positive"), &zero, c_bits.iter().cloned())?;

        let temp = affine_r.sub(cs.ns(|| "sub_recommit"), recommit)?;
        let negative_result = negative_result.add(cs.ns(|| "add_temp"), &temp)?;
        let positive_result = positive_result.add(cs.ns(|| "add_temp2"), &temp)?;

        let result = GG::conditionally_select(
            cs.ns(|| "select result"),
            &is_negative.not(),
            &positive_result,
            &negative_result,
        )?;

        result.enforce_equal(&mut cs.ns(|| "Check that the value balance commitment verifies"), &zero)?;

        Ok(())
    }
}
