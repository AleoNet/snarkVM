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
    algorithms::crypto_hash::PoseidonSpongeGadget,
    traits::ToConstraintFieldGadget,
    AlgebraicSpongeVar,
    AllocGadget,
    Boolean,
    CRHGadget,
    FpGadget,
};
use snarkvm_algorithms::{crh::PoseidonCRH, CRH};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use std::borrow::{Borrow, Cow};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoseidonCRHGadget<F: PrimeField, const INPUT_SIZE_FE: usize> {
    pub(crate) crh: PoseidonCRH<F, INPUT_SIZE_FE>,
}

impl<F: PrimeField, const INPUT_SIZE_FE: usize> AllocGadget<PoseidonCRH<F, INPUT_SIZE_FE>, F>
    for PoseidonCRHGadget<F, INPUT_SIZE_FE>
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PoseidonCRH<F, INPUT_SIZE_FE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self { crh: value_gen()?.borrow().clone() })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PoseidonCRH<F, INPUT_SIZE_FE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _f: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PoseidonCRH<F, INPUT_SIZE_FE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _f: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

impl<F: PrimeField, const INPUT_SIZE_FE: usize> CRHGadget<PoseidonCRH<F, INPUT_SIZE_FE>, F>
    for PoseidonCRHGadget<F, INPUT_SIZE_FE>
{
    type OutputGadget = FpGadget<F>;

    fn check_evaluation_gadget_on_bits<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        input: Vec<Boolean>,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        // Pad the input if necessary.
        let input = {
            let input_size_bits: usize = INPUT_SIZE_FE * <F as PrimeField>::Parameters::CAPACITY as usize;
            assert!(input.len() <= input_size_bits, "PoseidonCRHGadget input bits exceeds supported input size");

            let mut input = Cow::Borrowed(&input);
            if input.len() < input_size_bits {
                input.to_mut().resize(input_size_bits, Boolean::Constant(false));
            }
            input
        };

        let field_input = input.to_constraint_field(cs.ns(|| "convert input into field gadgets"))?;

        let mut sponge = PoseidonSpongeGadget::with_parameters(cs.ns(|| "alloc"), &self.crh.parameters().clone());
        sponge.absorb(cs.ns(|| "absorb"), field_input.iter())?;
        let res = sponge.squeeze(cs.ns(|| "squeeze"), 1)?;
        Ok(res[0].clone())
    }

    fn check_evaluation_gadget_on_field_elements<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        input: Vec<FpGadget<F>>,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        // Pad the input if necessary.
        let input = {
            assert!(input.len() <= INPUT_SIZE_FE);

            let mut input = Cow::Borrowed(&input);
            if input.len() < INPUT_SIZE_FE {
                input.to_mut().resize(INPUT_SIZE_FE, FpGadget::Constant(F::zero()));
            }
            input
        };

        let mut sponge = PoseidonSpongeGadget::with_parameters(cs.ns(|| "alloc"), self.crh.parameters());
        sponge.absorb(cs.ns(|| "absorb"), input.iter())?;
        let res = sponge.squeeze(cs.ns(|| "squeeze"), 1)?;
        Ok(res[0].clone())
    }
}
