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
    algorithms::crh::BoweHopwoodPedersenCRHGadget,
    integers::uint::UInt8,
    traits::{
        algorithms::{CRHGadget, CommitmentGadget},
        alloc::AllocGadget,
        curves::CurveGadget,
        integers::integer::Integer,
    },
};
use snarkvm_algorithms::{commitment::BHPCommitmentScheme, CommitmentScheme};
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoweHopwoodPedersenCommitmentGadget<
    G: ProjectiveCurve,
    F: PrimeField,
    GG: CurveGadget<G, F>,
    const NUM_WINDOWS: usize,
    const WINDOW_SIZE: usize,
> {
    bhp_crh_gadget: BoweHopwoodPedersenCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>,
    random_base: Vec<G>,
}

// TODO (howardwu): This should be only `alloc_constant`. This is unsafe convention.
impl<G: ProjectiveCurve, F: PrimeField, GG: CurveGadget<G, F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    AllocGadget<BHPCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>, F>
    for BoweHopwoodPedersenCommitmentGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let bhp: BHPCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE> = value_gen()?.borrow().parameters().into();
        Ok(Self {
            bhp_crh_gadget: BoweHopwoodPedersenCRHGadget::alloc(cs, || Ok(bhp.bhp_crh.clone()))?,
            random_base: bhp.random_base,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let bhp: BHPCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE> = value_gen()?.borrow().parameters().into();
        Ok(Self {
            bhp_crh_gadget: BoweHopwoodPedersenCRHGadget::alloc_input(cs, || Ok(bhp.bhp_crh.clone()))?,
            random_base: bhp.random_base,
        })
    }
}

impl<F: PrimeField, G: ProjectiveCurve, GG: CurveGadget<G, F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    CommitmentGadget<BHPCommitmentScheme<G, NUM_WINDOWS, WINDOW_SIZE>, F>
    for BoweHopwoodPedersenCommitmentGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    type OutputGadget = GG;
    type RandomnessGadget = BHPRandomnessGadget<G>;

    fn check_commitment_gadget<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        input: &[UInt8],
        randomness: &Self::RandomnessGadget,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        assert!((input.len() * 8) <= (WINDOW_SIZE * NUM_WINDOWS));

        // Compute BHP CRH.
        let mut result = self
            .bhp_crh_gadget
            .check_evaluation_gadget(cs.ns(|| "BHP hash"), input.to_vec())?;

        // Compute h^r.
        let rand_bits = randomness.0.iter().flat_map(|byte| byte.to_bits_le());
        result.scalar_multiplication(cs.ns(|| "randomizer"), rand_bits.zip(&self.random_base))?;

        Ok(result)
    }
}
