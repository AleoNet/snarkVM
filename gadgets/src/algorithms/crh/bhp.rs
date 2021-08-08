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
    bits::Boolean,
    traits::{algorithms::CRHGadget, alloc::AllocGadget, curves::CurveGadget},
};
use snarkvm_algorithms::crh::{BHPCRH, BOWE_HOPWOOD_CHUNK_SIZE};
use snarkvm_curves::ProjectiveCurve;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use std::{borrow::Borrow, marker::PhantomData};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BHPCRHGadget<
    G: ProjectiveCurve,
    F: PrimeField,
    GG: CurveGadget<G, F>,
    const NUM_WINDOWS: usize,
    const WINDOW_SIZE: usize,
> {
    pub(crate) crh: BHPCRH<G, NUM_WINDOWS, WINDOW_SIZE>,
    _field: PhantomData<F>,
    _group: PhantomData<GG>,
}

impl<G: ProjectiveCurve, F: PrimeField, GG: CurveGadget<G, F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    AllocGadget<BHPCRH<G, NUM_WINDOWS, WINDOW_SIZE>, F> for BHPCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCRH<G, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            crh: value_gen()?.borrow().clone(),
            _field: PhantomData,
            _group: PhantomData,
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCRH<G, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BHPCRH<G, NUM_WINDOWS, WINDOW_SIZE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

impl<F: PrimeField, G: ProjectiveCurve, GG: CurveGadget<G, F>, const NUM_WINDOWS: usize, const WINDOW_SIZE: usize>
    CRHGadget<BHPCRH<G, NUM_WINDOWS, WINDOW_SIZE>, F> for BHPCRHGadget<G, F, GG, NUM_WINDOWS, WINDOW_SIZE>
{
    type OutputGadget = GG;

    fn check_evaluation_gadget_on_bits<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        input: Vec<Boolean>,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        // Pad the input bytes.
        let mut input_in_bits = input;
        input_in_bits.resize(WINDOW_SIZE * NUM_WINDOWS, Boolean::Constant(false));
        assert_eq!(input_in_bits.len(), WINDOW_SIZE * NUM_WINDOWS);

        if (input_in_bits.len()) % BOWE_HOPWOOD_CHUNK_SIZE != 0 {
            let current_length = input_in_bits.len();
            let target_length = current_length + BOWE_HOPWOOD_CHUNK_SIZE - current_length % BOWE_HOPWOOD_CHUNK_SIZE;
            input_in_bits.resize(target_length, Boolean::constant(false));
        }
        assert!(input_in_bits.len() % BOWE_HOPWOOD_CHUNK_SIZE == 0);
        assert_eq!(self.crh.bases.len(), NUM_WINDOWS);
        for generators in self.crh.bases.iter() {
            assert_eq!(generators.len(), WINDOW_SIZE);
        }

        // Allocate new variable for the result.
        let input_in_bits = input_in_bits
            .chunks(WINDOW_SIZE * BOWE_HOPWOOD_CHUNK_SIZE)
            .map(|x| x.chunks(BOWE_HOPWOOD_CHUNK_SIZE));

        Ok(GG::three_bit_signed_digit_scalar_multiplication(
            cs,
            &self.crh.bases,
            input_in_bits,
        )?)
    }
}
