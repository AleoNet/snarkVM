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
use snarkvm_algorithms::encoding::{PackedFieldsAndBytes, PackedFieldsAndBytesEncodingScheme};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use snarkvm_utilities::borrow::Borrow;
use std::marker::PhantomData;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PackedFieldsAndBytesEncodingGadget<F: PrimeField> {
    f_phantom: PhantomData<F>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PackedFieldsAndBytesGadget<F: PrimeField> {
    pub field_elements: Vec<FpGadget<F>>,
    pub remaining_bytes: Vec<UInt8>,
}

// Note: this function cannot take a function `value_gen` that is not compatible with the setup mode.
impl<F: PrimeField> AllocGadget<PackedFieldsAndBytes<F>, F> for PackedFieldsAndBytesGadget<F> {
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PackedFieldsAndBytes<F>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let f = value_gen()?;
        let val = f.borrow();

        let field_elements =
            Vec::<FpGadget<F>>::alloc_constant(cs.ns(|| "alloc field_elements"), || Ok(val.field_elements.clone()))?;
        let remaining_bytes = UInt8::constant_vec(&val.remaining_bytes);

        Ok(Self {
            field_elements,
            remaining_bytes,
        })
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<PackedFieldsAndBytes<F>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let f = value_gen()?;
        let val = f.borrow();

        let field_elements =
            Vec::<FpGadget<F>>::alloc(cs.ns(|| "alloc field_elements"), || Ok(val.field_elements.clone()))?;
        let remaining_bytes = UInt8::alloc_vec(cs.ns(|| "alloc remaining bytes"), &val.remaining_bytes)?;

        Ok(Self {
            field_elements,
            remaining_bytes,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PackedFieldsAndBytes<F>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let f = value_gen()?;
        let val = f.borrow();

        let field_elements =
            Vec::<FpGadget<F>>::alloc_input(cs.ns(|| "alloc field_elements"), || Ok(val.field_elements.clone()))?;
        let remaining_bytes = UInt8::alloc_input_vec_le(cs.ns(|| "alloc remaining bytes"), &val.remaining_bytes)?;

        Ok(Self {
            field_elements,
            remaining_bytes,
        })
    }
}

impl<F: PrimeField> ConditionalEqGadget<F> for PackedFieldsAndBytesGadget<F> {
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

impl<F: PrimeField> EqGadget<F> for PackedFieldsAndBytesGadget<F> {}

impl<F: PrimeField> ToBytesGadget<F> for PackedFieldsAndBytesGadget<F> {
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
        let mut res = vec![];

        let field_elements_len = UInt8::constant(self.field_elements.len() as u8);
        res.push(field_elements_len);

        for (i, elem) in self.field_elements.iter().enumerate() {
            res.extend_from_slice(&elem.to_bytes_strict(cs.ns(|| format!("to_bytes the field element {}", i)))?);
        }

        res.extend_from_slice(&self.remaining_bytes);

        Ok(res)
    }
}

impl<F: PrimeField> ToConstraintFieldGadget<F> for PackedFieldsAndBytesGadget<F> {
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

impl<F: PrimeField> EncodingGadget<PackedFieldsAndBytesEncodingScheme<F>, F> for PackedFieldsAndBytesEncodingGadget<F> {
    type DataGadget = Vec<UInt8>;
    type EncodedDataGadget = PackedFieldsAndBytesGadget<F>;

    fn enforce_encoding_correctness<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        data: &Self::DataGadget,
        encoded_data: &Self::EncodedDataGadget,
    ) -> Result<(), SynthesisError> {
        // Enforce the `encoded_data` has a reasonable amount of remaining bytes.
        let capacity = <F::Parameters as FieldParameters>::CAPACITY as usize;
        let cutoff_bytes = capacity / 8;
        assert!(encoded_data.remaining_bytes.len() <= cutoff_bytes);

        // Convert the `data` into bits.
        let mut left_bits = Vec::<Boolean>::with_capacity(data.len() * 8);

        for byte in data.iter() {
            let byte_bits = byte.to_bits_le();
            left_bits.extend_from_slice(&byte_bits);
        }

        // Convert the `encoded_data` into bits.
        let mut right_bits = Vec::<Boolean>::with_capacity(
            encoded_data.field_elements.len() * capacity + encoded_data.remaining_bytes.len() * 8,
        );

        for (i, elem) in encoded_data.field_elements.iter().enumerate() {
            let elem_bits = elem.to_bits_le(cs.ns(|| format!("to_bits encoded data element {}", i)))?;
            right_bits.extend_from_slice(&elem_bits[..capacity]);
        }
        for byte in encoded_data.remaining_bytes.iter() {
            let byte_bits = byte.to_bits_le();
            right_bits.extend_from_slice(&byte_bits);
        }

        // Truncate the ending zero bits in the encoded data.
        let additional_bits = right_bits.len() % 8;
        right_bits.truncate(right_bits.len() - additional_bits);

        if left_bits.len() != right_bits.len() {
            return Err(SynthesisError::Unsatisfiable);
        }

        left_bits.enforce_equal(cs.ns(|| "enforce consistency"), &right_bits)?;

        Ok(())
    }
}

impl<F: PrimeField> AllocGadget<PackedFieldsAndBytesEncodingScheme<F>, F> for PackedFieldsAndBytesEncodingGadget<F> {
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PackedFieldsAndBytesEncodingScheme<F>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _f: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self::default())
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PackedFieldsAndBytesEncodingScheme<F>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _f: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PackedFieldsAndBytesEncodingScheme<F>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _f: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}
