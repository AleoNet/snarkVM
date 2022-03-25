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

use crate::{
    algorithms::crh::PedersenCRHGadget,
    integers::uint::UInt8,
    traits::{
        algorithms::{CRHGadget, MaskedCRHGadget},
        alloc::AllocGadget,
        curves::CompressedGroupGadget,
    },
    Boolean,
};
use snarkvm_algorithms::{
    crh::{PedersenCRH, PedersenCompressedCRH},
    CRH,
};
use snarkvm_curves::AffineCurve;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use std::borrow::Borrow;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PedersenCompressedCRHGadget<
    G: AffineCurve,
    F: PrimeField,
    GG: CompressedGroupGadget<G, F>,
    const NUM_WINDOWS: usize,
    const WINDOW_SIZE: usize,
> {
    crh_gadget: PedersenCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>,
}

// TODO (howardwu): This should be only `alloc_constant`. This is unsafe convention.
impl<G: AffineCurve, F: PrimeField, GG: CompressedGroupGadget<G, F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    AllocGadget<PedersenCompressedCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>, F>
    for PedersenCompressedCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PedersenCompressedCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let crh: PedersenCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE> = value_gen()?.borrow().parameters().clone();
        Ok(Self {
            crh_gadget: PedersenCRHGadget::<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>::alloc_constant(cs, || Ok(crh))?,
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PedersenCompressedCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PedersenCompressedCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

impl<G: AffineCurve, F: PrimeField, GG: CompressedGroupGadget<G, F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    CRHGadget<PedersenCompressedCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>, F>
    for PedersenCompressedCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    type OutputGadget = GG::BaseFieldGadget;

    fn check_evaluation_gadget_on_bits<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        input: Vec<Boolean>,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        let output = self.crh_gadget.check_evaluation_gadget_on_bits(cs, input)?;
        Ok(output.to_x_coordinate())
    }
}

impl<G: AffineCurve, F: PrimeField, GG: CompressedGroupGadget<G, F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    MaskedCRHGadget<PedersenCompressedCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>, F>
    for PedersenCompressedCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    type MaskParametersGadget = Self;

    fn check_evaluation_gadget_masked<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        input: Vec<UInt8>,
        mask_parameters: &Self::MaskParametersGadget,
        mask: Vec<UInt8>,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        let output = self.crh_gadget.check_evaluation_gadget_masked(cs, input, &mask_parameters.crh_gadget, mask)?;
        Ok(output.to_x_coordinate())
    }
}
