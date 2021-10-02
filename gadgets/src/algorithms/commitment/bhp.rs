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
    algorithms::crh::BHPCRHGadget,
    integers::uint::UInt8,
    traits::{
        algorithms::CommitmentGadget,
        alloc::AllocGadget,
        curves::CompressedGroupGadget,
        integers::integer::Integer,
    },
    ToBitsLEGadget,
    ToBytesGadget,
};
use snarkvm_algorithms::{commitment::BHPCommitment, CommitmentScheme};
use snarkvm_curves::ProjectiveCurve;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::{to_bytes_le, ToBytes};

use std::{borrow::Borrow, marker::PhantomData};

#[derive(Clone, Debug)]
pub struct BHPRandomnessGadget<G: ProjectiveCurve>(pub Vec<UInt8>, PhantomData<G>);

impl<G: ProjectiveCurve, F: PrimeField> AllocGadget<G::ScalarField, F> for BHPRandomnessGadget<G> {
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<G::ScalarField>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let randomness = to_bytes_le![value_gen()?.borrow()].unwrap();
        Ok(Self(UInt8::alloc_vec(cs, &randomness)?, PhantomData))
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<G::ScalarField>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let randomness = to_bytes_le![value_gen()?.borrow()].unwrap();
        Ok(Self(UInt8::alloc_input_vec_le(cs, &randomness)?, PhantomData))
    }
}

impl<G: ProjectiveCurve, F: PrimeField> ToBytesGadget<F> for BHPRandomnessGadget<G> {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.to_bytes_strict(cs)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BHPCommitmentGadget<
    G: ProjectiveCurve,
    F: PrimeField,
    GG: CompressedGroupGadget<G, F>,
    const NUM_WINDOWS: usize,
    const WINDOW_SIZE: usize,
> {
    bhp_crh_gadget: BHPCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>,
    random_base: Vec<G>,
}

impl<
    G: ProjectiveCurve,
    F: PrimeField,
    GG: CompressedGroupGadget<G, F>,
    const NUM_WINDOWS: usize,
    const WINDOW_SIZE: usize,
> AllocGadget<BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE>, F>
    for BHPCommitmentGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let bhp: BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE> = value_gen()?.borrow().parameters().into();
        Ok(Self {
            bhp_crh_gadget: BHPCRHGadget::alloc_constant(cs, || Ok(bhp.bhp_crh.clone()))?,
            random_base: bhp.random_base,
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

impl<
    F: PrimeField,
    G: ProjectiveCurve,
    GG: CompressedGroupGadget<G, F>,
    const NUM_WINDOWS: usize,
    const WINDOW_SIZE: usize,
> CommitmentGadget<BHPCommitment<G, NUM_WINDOWS, WINDOW_SIZE>, F>
    for BHPCommitmentGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    type OutputGadget = GG::BaseFieldGadget;
    type RandomnessGadget = BHPRandomnessGadget<G>;

    fn check_commitment_gadget<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        input: &[UInt8],
        randomness: &Self::RandomnessGadget,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        assert!((input.len() * 8) <= (WINDOW_SIZE * NUM_WINDOWS));

        // Compute BHP CRH.
        let input = input.to_vec().to_bits_le(cs.ns(|| "to_bits"))?;
        let mut result = self
            .bhp_crh_gadget
            .check_evaluation_gadget_on_bits_inner(cs.ns(|| "BHP hash"), input)?;

        // Compute h^r.
        let rand_bits = randomness.0.iter().flat_map(|byte| byte.to_bits_le());
        result.scalar_multiplication(cs.ns(|| "randomizer"), rand_bits.zip(&self.random_base))?;

        Ok(result.to_x_coordinate())
    }
}
