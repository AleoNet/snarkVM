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

use std::{borrow::Borrow, marker::PhantomData};

use snarkvm_curves::traits::{ModelParameters, MontgomeryParameters};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::{to_bytes_le, ToBytes};

use crate::{
    bits::{Boolean, ToBitsBEGadget, ToBytesBEGadget, ToBytesLEGadget},
    fields::FpGadget,
    integers::uint::UInt8,
    traits::alloc::AllocGadget,
};

#[derive(Clone, Debug)]
pub struct Elligator2FieldGadget<P: MontgomeryParameters, F: PrimeField>(pub FpGadget<F>, PhantomData<P>);

impl<P: MontgomeryParameters, F: PrimeField> AllocGadget<<P as ModelParameters>::BaseField, F>
    for Elligator2FieldGadget<P, F>
{
    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<<P as ModelParameters>::BaseField>,
        CS: ConstraintSystem<F>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Elligator2FieldGadget(
            FpGadget::alloc(cs, || match value_gen() {
                Ok(value) => Ok(F::read_le(&to_bytes_le![value.borrow()]?[..])?),
                Err(_) => Err(SynthesisError::AssignmentMissing),
            })?,
            PhantomData,
        ))
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<<P as ModelParameters>::BaseField>,
        CS: ConstraintSystem<F>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Elligator2FieldGadget(
            FpGadget::alloc_input(cs, || match value_gen() {
                Ok(value) => Ok(F::read_le(&to_bytes_le![value.borrow()]?[..])?),
                Err(_) => Err(SynthesisError::AssignmentMissing),
            })?,
            PhantomData,
        ))
    }
}

impl<P: MontgomeryParameters, F: PrimeField> ToBitsBEGadget<F> for Elligator2FieldGadget<P, F> {
    fn to_bits_be<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        self.0.to_bits_be(cs)
    }

    fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        self.0.to_bits_be_strict(cs)
    }
}

impl<P: MontgomeryParameters, F: PrimeField> ToBytesLEGadget<F> for Elligator2FieldGadget<P, F> {
    fn to_bytes_le<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.to_bytes_le(cs)
    }

    fn to_bytes_le_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.to_bytes_le_strict(cs)
    }
}

impl<P: MontgomeryParameters, F: PrimeField> ToBytesBEGadget<F> for Elligator2FieldGadget<P, F> {
    fn to_bytes_be<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.to_bytes_be(cs)
    }

    fn to_bytes_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.to_bytes_be_strict(cs)
    }
}
