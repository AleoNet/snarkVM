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

use std::fmt::Debug;

use snarkvm_fields::{Field, FieldParameters, PrimeField, ToConstraintField};
use snarkvm_r1cs::{errors::SynthesisError, Assignment, ConstraintSystem, LinearCombination};
use snarkvm_utilities::ToBytes;

use crate::{
    bits::{
        boolean::{AllocatedBit, Boolean},
        FromBitsBEGadget,
        FromBitsLEGadget,
        FromBytesBEGadget,
        FromBytesLEGadget,
        ToBitsBEGadget,
        ToBitsLEGadget,
        ToBytesBEGadget,
        ToBytesLEGadget,
    },
    fields::FpGadget,
    traits::{
        alloc::AllocGadget,
        eq::{ConditionalEqGadget, EqGadget},
        integers::Integer,
        select::CondSelectGadget,
    },
    UnsignedIntegerError,
};

uint_impl!(UInt8, u8, 8);
uint_impl!(UInt16, u16, 16);
uint_impl!(UInt32, u32, 32);
uint_impl!(UInt64, u64, 64);

pub trait UInt: Integer {
    /// Returns the inverse `UInt`
    fn negate(&self) -> Self;

    /// Rotate self bits by size
    fn rotr(&self, by: usize) -> Self;

    /// Perform modular addition of several `UInt` objects.
    fn addmany<F: PrimeField, CS: ConstraintSystem<F>>(cs: CS, operands: &[Self]) -> Result<Self, SynthesisError>;

    /// Perform Bitwise multiplication of two `UInt` objects.
    /// Reference: https://en.wikipedia.org/wiki/Binary_multiplier
    fn mul<F: PrimeField, CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Self, UnsignedIntegerError>;
}

// These methods are used throughout snarkvm-gadgets exclusively by UInt8
impl UInt8 {
    /// Construct a constant vector of `UInt8` from a vector of `u8`
    pub fn constant_vec(values: &[u8]) -> Vec<Self> {
        values.iter().copied().map(UInt8::constant).collect()
    }

    pub fn alloc_vec<F, CS, T>(mut cs: CS, values: &[T]) -> Result<Vec<Self>, SynthesisError>
    where
        F: Field,
        CS: ConstraintSystem<F>,
        T: Into<Option<u8>> + Copy,
    {
        let mut output_vec = Vec::with_capacity(values.len());
        for (i, value) in values.iter().enumerate() {
            let byte: Option<u8> = Into::into(*value);
            let alloc_byte = Self::alloc(&mut cs.ns(|| format!("byte_{}", i)), || byte.get())?;
            output_vec.push(alloc_byte);
        }
        Ok(output_vec)
    }

    /// Allocates a vector of `u8`'s by first converting (chunks of) them to
    /// `F` elements, (thus reducing the number of input allocations),
    /// and then converts this list of `F` gadgets back into
    /// bytes.
    pub fn alloc_input_vec_le<F, CS>(mut cs: CS, values: &[u8]) -> Result<Vec<Self>, SynthesisError>
    where
        F: PrimeField,
        CS: ConstraintSystem<F>,
    {
        let values_len = values.len();
        let field_elements: Vec<F> = ToConstraintField::<F>::to_field_elements(values).unwrap();

        let max_size = 8 * (F::Parameters::CAPACITY / 8) as usize;
        let mut allocated_bits = Vec::new();
        for (i, field_element) in field_elements.into_iter().enumerate() {
            let fe = FpGadget::alloc_input(&mut cs.ns(|| format!("Field element {}", i)), || Ok(field_element))?;
            let mut fe_bits = fe.to_bits_be(cs.ns(|| format!("Convert fe to bits {}", i)))?;
            // FpGadget::to_bits outputs a big-endian binary representation of
            // fe_gadget's value, so we have to reverse it to get the little-endian
            // form.
            fe_bits.reverse();

            // Remove the most significant bit, because we know it should be zero
            // because `values.to_field_elements()` only
            // packs field elements up to the penultimate bit.
            // That is, the most significant bit (`F::NUM_BITS`-th bit) is
            // unset, so we can just pop it off.
            allocated_bits.extend_from_slice(&fe_bits[0..max_size]);
        }

        // Chunk up slices of 8 bit into bytes.
        Ok(allocated_bits[0..8 * values_len]
            .chunks(8)
            .map(Self::u8_from_bits_le)
            .flatten()
            .collect())
    }

    /// Returns a vector of `Boolean` gadget bits in little-endian order.
    /// Gadget implementations and Leo functions should call `ToBitsLEGadget` instead.
    pub fn u8_to_bits_le(&self) -> Vec<Boolean> {
        self.bits.clone()
    }

    /// Returns a `UInt8` gadget from a vector of `Boolean` gadget bits in little-endian order.
    /// Gadget implementations and Leo functions should call `FromBitsLEGadget` instead.
    pub fn u8_from_bits_le(bits: &[Boolean]) -> Result<Self, SynthesisError> {
        if bits.len() != 8 {
            return Err(SynthesisError::Unsatisfiable);
        }

        let mut value = Some(0u8);
        for b in bits.iter().rev() {
            value.as_mut().map(|v| *v <<= 1);

            match *b {
                Boolean::Constant(b) => {
                    if b {
                        value.as_mut().map(|v| *v |= 1);
                    }
                }
                Boolean::Is(ref b) => match b.get_value() {
                    Some(true) => {
                        value.as_mut().map(|v| *v |= 1);
                    }
                    Some(false) => {}
                    None => value = None,
                },
                Boolean::Not(ref b) => match b.get_value() {
                    Some(false) => {
                        value.as_mut().map(|v| *v |= 1);
                    }
                    Some(true) => {}
                    None => value = None,
                },
            }
        }

        Ok(Self {
            value: value.map(|x| x as u8),
            bits: bits.to_vec(),
            negated: false,
        })
    }
}

impl UInt32 {
    /// Returns a eight `UInt8` gadget bits in little-endian order from a `UInt32`.
    /// Gadget implementations and Leo functions should call `FromBitsLEGadget` instead.
    pub fn u32_to_bytes_le<F: Field, CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        const BYTES_SIZE: usize = 8; // Fix bytes size to 8 for blake2s

        let value_chunks = match self.value.map(|val| {
            let mut bytes = [0u8; BYTES_SIZE];
            val.write_le(bytes.as_mut()).unwrap();
            bytes
        }) {
            Some(chunks) => [Some(chunks[0]), Some(chunks[1]), Some(chunks[2]), Some(chunks[3])],
            None => [None, None, None, None],
        };

        let bits = self.to_bits_le(&mut cs.ns(|| "to_bits_le"))?;
        let mut bytes = Vec::with_capacity(bits.len() / 8);
        for (chunk8, value) in bits.chunks(8).into_iter().zip(value_chunks.iter()) {
            let byte = UInt8 {
                bits: chunk8.to_vec(),
                negated: false,
                value: *value,
            };
            bytes.push(byte);
        }

        Ok(bytes)
    }

    /// Returns a `UInt32` gadget from a vector of `Boolean` gadget bits in little-endian order.
    /// Gadget implementations and Leo functions should call `FromBitsLEGadget` instead.
    pub fn u32_from_bits_le(bits: &[Boolean]) -> Result<Self, SynthesisError> {
        if bits.len() != 32 {
            return Err(SynthesisError::Unsatisfiable);
        }

        let mut value = Some(0u32);
        for b in bits.iter().rev() {
            value.as_mut().map(|v| *v <<= 1);

            match *b {
                Boolean::Constant(b) => {
                    if b {
                        value.as_mut().map(|v| *v |= 1);
                    }
                }
                Boolean::Is(ref b) => match b.get_value() {
                    Some(true) => {
                        value.as_mut().map(|v| *v |= 1);
                    }
                    Some(false) => {}
                    None => value = None,
                },
                Boolean::Not(ref b) => match b.get_value() {
                    Some(false) => {
                        value.as_mut().map(|v| *v |= 1);
                    }
                    Some(true) => {}
                    None => value = None,
                },
            }
        }

        Ok(Self {
            value: value.map(|x| x as u32),
            bits: bits.to_vec(),
            negated: false,
        })
    }
}
