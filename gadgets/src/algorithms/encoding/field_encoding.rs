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
    AllocGadget,
    Boolean,
    ConditionalEqGadget,
    EncodingGadget,
    EqGadget,
    FpGadget,
    Integer,
    ToBitsLEGadget,
    ToBytesGadget,
    ToConstraintFieldGadget,
    UInt8,
};
use snarkvm_algorithms::encoding::{FieldEncodedData, FieldEncodingScheme};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use snarkvm_utilities::borrow::Borrow;
use std::marker::PhantomData;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FieldEncodedDataGadget<F: PrimeField> {
    pub field_elements: Vec<FpGadget<F>>,
    pub remaining_bytes: Vec<UInt8>,
}

// Note: this function cannot take a function `value_gen` that is not compatible with the setup mode.
impl<F: PrimeField> AllocGadget<FieldEncodedData<F>, F> for FieldEncodedDataGadget<F> {
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldEncodedData<F>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let encoded = value.borrow();
        let field_elements =
            Vec::alloc_constant(cs.ns(|| "alloc field_elements"), || Ok(encoded.field_elements.clone()))?;
        let remaining_bytes = UInt8::constant_vec(&encoded.remaining_bytes);
        Ok(Self {
            field_elements,
            remaining_bytes,
        })
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<FieldEncodedData<F>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let encoded = value.borrow();
        let field_elements = Vec::alloc(cs.ns(|| "alloc field_elements"), || Ok(encoded.field_elements.clone()))?;
        let remaining_bytes = UInt8::alloc_vec(cs.ns(|| "alloc remaining bytes"), &encoded.remaining_bytes)?;
        Ok(Self {
            field_elements,
            remaining_bytes,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldEncodedData<F>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let encoded = value.borrow();
        let field_elements = Vec::alloc_input(cs.ns(|| "alloc field_elements"), || Ok(encoded.field_elements.clone()))?;
        let remaining_bytes = UInt8::alloc_input_vec_le(cs.ns(|| "alloc remaining bytes"), &encoded.remaining_bytes)?;
        Ok(Self {
            field_elements,
            remaining_bytes,
        })
    }
}

impl<F: PrimeField> ConditionalEqGadget<F> for FieldEncodedDataGadget<F> {
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        assert_eq!(self.field_elements.len(), other.field_elements.len());
        assert_eq!(self.remaining_bytes.len(), other.remaining_bytes.len());

        self.field_elements
            .conditional_enforce_equal(cs.ns(|| "field_elements"), &other.field_elements, condition)?;
        self.remaining_bytes.conditional_enforce_equal(
            cs.ns(|| "remaining_bytes"),
            &other.remaining_bytes,
            condition,
        )?;

        Ok(())
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

impl<F: PrimeField> EqGadget<F> for FieldEncodedDataGadget<F> {}

impl<F: PrimeField> ToBytesGadget<F> for FieldEncodedDataGadget<F> {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut res = vec![];

        let field_elements_len = UInt8::constant(self.field_elements.len() as u8);
        res.push(field_elements_len);

        for (i, elem) in self.field_elements.iter().enumerate() {
            res.extend_from_slice(&elem.to_bytes(cs.ns(|| format!("to_bytes the field element {}", i)))?);
        }

        res.extend_from_slice(&self.remaining_bytes);

        Ok(res)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

impl<F: PrimeField> ToConstraintFieldGadget<F> for FieldEncodedDataGadget<F> {
    fn to_constraint_field<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<FpGadget<F>>, SynthesisError> {
        let mut res = self.field_elements.clone();
        if !self.remaining_bytes.is_empty() {
            res.extend_from_slice(
                &self
                    .remaining_bytes
                    .to_constraint_field(cs.ns(|| "convert remaining bytes into field elements"))?,
            );
        }
        Ok(res)
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FieldEncodingGadget<F: PrimeField> {
    f_phantom: PhantomData<F>,
}

impl<F: PrimeField> AllocGadget<FieldEncodingScheme<F>, F> for FieldEncodingGadget<F> {
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldEncodingScheme<F>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _f: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self::default())
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<FieldEncodingScheme<F>>, CS: ConstraintSystem<F>>(
        _cs: CS,
        _f: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldEncodingScheme<F>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _f: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

impl<F: PrimeField> EncodingGadget<FieldEncodingScheme<F>, F> for FieldEncodingGadget<F> {
    type DataGadget = Vec<UInt8>;
    type EncodedDataGadget = FieldEncodedDataGadget<F>;

    /// Enforces that given data and encoded data matches in their bit representation.
    fn enforce_encoding_correctness<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        data: &Self::DataGadget,
        encoded_data: &Self::EncodedDataGadget,
    ) -> Result<(), SynthesisError> {
        // Enforce the `encoded_data` has a reasonable amount of remaining bytes.
        let field_capacity = <F::Parameters as FieldParameters>::CAPACITY as usize;
        assert!(
            encoded_data.remaining_bytes.len() <= (field_capacity / 8),
            "Remaining bytes should fit within 1 field element"
        );

        // Convert the `data` into bits.
        let mut data_bits = Vec::<Boolean>::with_capacity(data.len() * 8);
        for byte in data.iter() {
            data_bits.extend_from_slice(&byte.to_bits_le());
        }

        // Convert the `encoded_data` into bits.
        let encoded_data_capacity =
            encoded_data.field_elements.len() * field_capacity + encoded_data.remaining_bytes.len() * 8;
        let mut encoded_data_bits = Vec::<Boolean>::with_capacity(encoded_data_capacity);
        for (i, element) in encoded_data.field_elements.iter().enumerate() {
            let element_bits = element.to_bits_le(cs.ns(|| format!("to_bits encoded data element {}", i)))?;
            encoded_data_bits.extend_from_slice(&element_bits[..field_capacity]);
        }
        for byte in encoded_data.remaining_bytes.iter() {
            encoded_data_bits.extend_from_slice(&byte.to_bits_le());
        }

        // Truncate the ending zero bits in the encoded data.
        let additional_bits = encoded_data_bits.len() % 8;
        encoded_data_bits.truncate(encoded_data_bits.len() - additional_bits);

        if data_bits.len() != encoded_data_bits.len() {
            return Err(SynthesisError::Unsatisfiable);
        }

        data_bits.enforce_equal(cs.ns(|| "enforce consistency"), &encoded_data_bits)?;

        Ok(())
    }
}
