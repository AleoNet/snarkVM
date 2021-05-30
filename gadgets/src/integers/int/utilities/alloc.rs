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
    bits::{Boolean, ToBitsBEGadget},
    fields::FpGadget,
    integers::int::*,
    traits::{
        integers::Integer,
        utilities::{alloc::AllocGadget, eq::EqGadget},
    },
};
use snarkvm_fields::{FieldParameters, PrimeField, ToConstraintField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

/// Alloc the unsigned integer through field elements rather purely bits
/// to reduce the number of input allocations.
macro_rules! alloc_input_fe {
    ($($gadget: ident)*) => ($(
        impl $gadget {
            /// Allocates the unsigned integer gadget by first converting
            /// the little-endian byte representation of the unsigned integer to
            /// `F` elements, (thus reducing the number of input allocations),
            /// and then converts this list of `F` gadgets into the unsigned integer gadget
            pub fn alloc_input_fe<F, CS>(mut cs: CS, value: <$gadget as Integer>::IntegerType) -> Result<Self, SynthesisError>
            where
                F: PrimeField,
                CS: ConstraintSystem<F>,
            {
                let value_bytes = value.to_le_bytes();
                let field_elements: Vec<F> = ToConstraintField::<F>::to_field_elements(&value_bytes[..]).unwrap();

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

                // Assert that the extra bits are false
                for (i, bit) in allocated_bits.iter().skip(<$gadget as Integer>::SIZE).enumerate() {
                    bit.enforce_equal(&mut cs.ns(|| format!("bit {} is false", i + <$gadget as Integer>::SIZE)), &Boolean::constant(false))?;
                }

                let bits = allocated_bits[0..<$gadget as Integer>::SIZE].to_vec();

                Ok(Self {
                    bits,
                    value: Some(value),
                })
            }
        }
    )*)
}

alloc_input_fe!(Int8 Int16 Int32 Int64 Int128);
