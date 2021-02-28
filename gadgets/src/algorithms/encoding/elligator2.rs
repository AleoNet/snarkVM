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

use crate::fields::FpGadget;
use crate::traits::utilities::alloc::AllocGadget;
use crate::traits::utilities::boolean::Boolean;
use crate::traits::utilities::uint::UInt8;
use crate::traits::utilities::ToBitsGadget;
use crate::traits::utilities::ToBytesGadget;
use snarkvm_curves::traits::ModelParameters;
use snarkvm_curves::traits::MontgomeryModelParameters;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::errors::SynthesisError;
use snarkvm_r1cs::ConstraintSystem;
use snarkvm_utilities::to_bytes;
use snarkvm_utilities::ToBytes;

use std::borrow::Borrow;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct Elligator2FieldGadget<P: MontgomeryModelParameters, F: PrimeField>(pub FpGadget<F>, PhantomData<P>);

impl<P: MontgomeryModelParameters, F: PrimeField> AllocGadget<<P as ModelParameters>::BaseField, F>
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
                Ok(value) => Ok(F::read(&to_bytes![value.borrow()]?[..])?),
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
                Ok(value) => Ok(F::read(&to_bytes![value.borrow()]?[..])?),
                Err(_) => Err(SynthesisError::AssignmentMissing),
            })?,
            PhantomData,
        ))
    }
}

impl<P: MontgomeryModelParameters, F: PrimeField> ToBitsGadget<F> for Elligator2FieldGadget<P, F> {
    fn to_bits<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.0.to_bits(cs)?)
    }

    fn to_bits_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.0.to_bits_strict(cs)?)
    }
}

impl<P: MontgomeryModelParameters, F: PrimeField> ToBytesGadget<F> for Elligator2FieldGadget<P, F> {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        Ok(self.0.to_bytes(cs)?)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        Ok(self.0.to_bytes_strict(cs)?)
    }
}
