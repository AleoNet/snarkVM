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
    bits::Boolean,
    traits::{algorithms::CRHGadget, alloc::AllocGadget, curves::CompressedGroupGadget},
};
use snarkvm_algorithms::crh::{BHPCRH, BHP_CHUNK_SIZE};
use snarkvm_curves::AffineCurve;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use std::{borrow::Borrow, marker::PhantomData};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BHPCRHGadget<
    G: AffineCurve,
    F: PrimeField,
    GG: CompressedGroupGadget<G, F>,
    const NUM_WINDOWS: usize,
    const WINDOW_SIZE: usize,
> {
    pub(crate) crh: BHPCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>,
    _field: PhantomData<F>,
    _group: PhantomData<GG>,
}

impl<G: AffineCurve, F: PrimeField, GG: CompressedGroupGadget<G, F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    AllocGadget<BHPCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>, F>
    for BHPCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self { crh: value_gen()?.borrow().clone(), _field: PhantomData, _group: PhantomData })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

impl<F: PrimeField, G: AffineCurve, GG: CompressedGroupGadget<G, F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    CRHGadget<BHPCRH<G::Projective, NUM_WINDOWS, WINDOW_SIZE>, F> for BHPCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    type OutputGadget = GG::BaseFieldGadget;

    fn check_evaluation_gadget_on_bits<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        input: Vec<Boolean>,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        let output = self.check_evaluation_gadget_on_bits_inner(cs, input)?;
        Ok(output.to_x_coordinate())
    }
}

impl<F: PrimeField, G: AffineCurve, GG: CompressedGroupGadget<G, F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    BHPCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    pub(crate) fn check_evaluation_gadget_on_bits_inner<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        input: Vec<Boolean>,
    ) -> Result<GG, SynthesisError> {
        assert!(input.len() <= WINDOW_SIZE * NUM_WINDOWS * BHP_CHUNK_SIZE);

        // Pad the input bytes.
        let mut input_in_bits = input;
        if (input_in_bits.len()) % BHP_CHUNK_SIZE != 0 {
            let padding = BHP_CHUNK_SIZE - (input_in_bits.len() % BHP_CHUNK_SIZE);
            input_in_bits.extend_from_slice(&vec![Boolean::constant(false); padding]);
        }
        assert!(input_in_bits.len() % BHP_CHUNK_SIZE == 0);

        let input_in_bits = input_in_bits.chunks(WINDOW_SIZE * BHP_CHUNK_SIZE).map(|x| x.chunks(BHP_CHUNK_SIZE));

        GG::three_bit_signed_digit_scalar_multiplication(cs, &self.crh.bases, input_in_bits)
    }
}
