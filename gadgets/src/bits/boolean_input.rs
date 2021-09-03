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

use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use snarkvm_utilities::{FromBits, ToBits};

use crate::{
    bits::{Boolean, ToBitsLEGadget},
    fields::FpGadget,
    traits::alloc::AllocGadget,
    FromFieldElementsGadget,
};

/// Conversion of field elements by converting them to boolean sequences
/// Used by Groth16 and Gm17
#[derive(Clone)]
pub struct BooleanInputGadget<F: PrimeField, CF: PrimeField> {
    pub val: Vec<Vec<Boolean>>,
    _snark_field: PhantomData<F>,
    _constraint_field: PhantomData<CF>,
}

impl<F: PrimeField, CF: PrimeField> BooleanInputGadget<F, CF> {
    pub fn new(val: Vec<Vec<Boolean>>) -> Self {
        Self {
            val,
            _snark_field: PhantomData,
            _constraint_field: PhantomData,
        }
    }
}

impl<F: PrimeField, CF: PrimeField> IntoIterator for BooleanInputGadget<F, CF> {
    type IntoIter = std::vec::IntoIter<Vec<Boolean>>;
    type Item = Vec<Boolean>;

    fn into_iter(self) -> Self::IntoIter {
        self.val.into_iter()
    }
}

impl<F: PrimeField, CF: PrimeField> AllocGadget<Vec<F>, CF> for BooleanInputGadget<F, CF> {
    fn alloc_constant<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<Vec<F>>, CS: ConstraintSystem<CF>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?;

        // convert the elements into booleans (little-endian)
        let mut res = Vec::<Vec<Boolean>>::new();
        for (i, elem) in obj.borrow().iter().enumerate() {
            let mut bits = elem.to_repr().to_bits_le();
            bits.truncate(F::size_in_bits());

            let mut booleans = Vec::<Boolean>::new();
            for (j, bit) in bits.iter().enumerate() {
                booleans.push(Boolean::alloc_constant(
                    cs.ns(|| format!("alloc_constant_bit_{}_{}", i, j)),
                    || Ok(*bit),
                )?);
            }

            res.push(booleans);
        }

        Ok(Self {
            val: res,
            _snark_field: PhantomData,
            _constraint_field: PhantomData,
        })
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<Vec<F>>, CS: ConstraintSystem<CF>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?;

        // convert the elements into booleans (little-endian)
        let mut res = Vec::<Vec<Boolean>>::new();
        for (i, elem) in obj.borrow().iter().enumerate() {
            let mut bits = elem.to_repr().to_bits_le();
            bits.truncate(F::size_in_bits());

            let mut booleans = Vec::<Boolean>::new();
            for (j, bit) in bits.iter().enumerate() {
                booleans.push(Boolean::alloc(cs.ns(|| format!("alloc_bit_{}_{}", i, j)), || Ok(*bit))?);
            }

            res.push(booleans);
        }

        Ok(Self {
            val: res,
            _snark_field: PhantomData,
            _constraint_field: PhantomData,
        })
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<Vec<F>>, CS: ConstraintSystem<CF>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?;

        // Step 1: obtain the bits of the F field elements (little-endian)
        let mut src_bits = Vec::<bool>::new();
        for elem in obj.borrow().iter() {
            let mut bits = elem.to_repr().to_bits_le();
            bits.truncate(F::size_in_bits());
            for _ in bits.len()..F::size_in_bits() {
                bits.push(false);
            }
            bits.reverse();

            src_bits.append(&mut bits);
        }

        // Step 2: repack the bits as CF field elements
        // Deciding how many bits can be embedded,
        //  if CF has the same number of bits as F, but is larger,
        //  then it is okay to put the entire field element in.
        let capacity = if CF::size_in_bits() == F::size_in_bits() {
            let fq = <<CF as PrimeField>::Parameters as FieldParameters>::MODULUS;
            let fr = <<F as PrimeField>::Parameters as FieldParameters>::MODULUS;

            let fq_u64: &[u64] = fq.as_ref();
            let fr_u64: &[u64] = fr.as_ref();

            let mut fq_not_smaller_than_fr = true;
            for (left, right) in fq_u64.iter().zip(fr_u64.iter()).rev() {
                if left < right {
                    fq_not_smaller_than_fr = false;
                    break;
                }

                if left > right {
                    break;
                }
            }

            if fq_not_smaller_than_fr {
                CF::size_in_bits()
            } else {
                CF::size_in_bits() - 1
            }
        } else {
            CF::size_in_bits() - 1
        };

        // Step 3: allocate the CF field elements as input
        let mut src_booleans = Vec::<Boolean>::new();
        for (i, chunk) in src_bits.chunks(capacity).enumerate() {
            let elem = CF::from_repr(<CF as PrimeField>::BigInteger::from_bits_be(chunk)).unwrap(); // big endian

            let elem_gadget = FpGadget::<CF>::alloc_input(cs.ns(|| format!("alloc_elem_{}", i)), || Ok(elem))?;
            let mut booleans = elem_gadget.to_bits_le(cs.ns(|| format!("elem_to_bits_{}", i)))?;
            booleans.truncate(chunk.len());
            booleans.reverse();

            src_booleans.append(&mut booleans);
        }

        // Step 4: unpack them back to bits
        let res = src_booleans
            .chunks(F::size_in_bits())
            .map(|f| {
                let mut res = f.to_vec();
                res.reverse();
                res
            })
            .collect::<Vec<Vec<Boolean>>>();

        Ok(Self {
            val: res,
            _snark_field: PhantomData,
            _constraint_field: PhantomData,
        })
    }
}

impl<F: PrimeField, CF: PrimeField> FromFieldElementsGadget<F, CF> for BooleanInputGadget<F, CF> {
    fn from_field_elements<CS: ConstraintSystem<CF>>(
        mut cs: CS,
        field_elements: &Vec<FpGadget<CF>>,
    ) -> Result<Self, SynthesisError> {
        // Step 1: obtain the booleans of the CF field variables
        let mut src_booleans = Vec::<Boolean>::new();
        for (i, elem) in field_elements.iter().enumerate() {
            let mut bits = elem.to_bits_le(cs.ns(|| format!("to_bits_le_{}", i)))?;
            bits.reverse();
            src_booleans.extend_from_slice(&bits);
        }

        // Step 2: repack the bits as F field elements
        // Deciding how many bits can be embedded.
        let capacity = if CF::size_in_bits() == F::size_in_bits() {
            let fq = <<CF as PrimeField>::Parameters as FieldParameters>::MODULUS;
            let fr = <<F as PrimeField>::Parameters as FieldParameters>::MODULUS;

            let fq_u64: &[u64] = fq.as_ref();
            let fr_u64: &[u64] = fr.as_ref();

            let mut fr_not_smaller_than_fq = true;
            for (left, right) in fr_u64.iter().zip(fq_u64.iter()).rev() {
                if left < right {
                    fr_not_smaller_than_fq = false;
                    break;
                }

                if left > right {
                    break;
                }
            }

            if fr_not_smaller_than_fq {
                F::size_in_bits()
            } else {
                F::size_in_bits() - 1
            }
        } else {
            F::size_in_bits() - 1
        };

        // Step 3: group them based on the used capacity of F
        let res = src_booleans
            .chunks(capacity)
            .map(|x| {
                let mut res = x.to_vec();
                res.reverse();
                res
            })
            .collect::<Vec<Vec<Boolean>>>();
        Ok(Self {
            val: res,
            _snark_field: PhantomData,
            _constraint_field: PhantomData,
        })
    }
}

#[cfg(test)]
mod test {

    use snarkvm_fields::PrimeField;
    use snarkvm_r1cs::{Fr, TestConstraintSystem};
    use snarkvm_utilities::{
        rand::{test_rng, UniformRand},
        to_bytes_le, ToBytes,
    };

    use super::*;
    use crate::{integers::uint::UInt8, traits::eq::EqGadget};

    fn field_element_to_bytes<F: PrimeField, CS: ConstraintSystem<F>>(
        mut cs: CS,
        field_elements: Vec<F>,
    ) -> Vec<Vec<UInt8>> {
        if field_elements.len() <= 1 {
            vec![UInt8::alloc_input_vec_le(
                cs.ns(|| format!("Allocate field elements")),
                &to_bytes_le![field_elements].unwrap(),
            )
            .unwrap()]
        } else {
            let mut fe_bytes = Vec::with_capacity(field_elements.len());
            for (index, field_element) in field_elements.iter().enumerate() {
                fe_bytes.push(
                    UInt8::alloc_input_vec_le(
                        cs.ns(|| format!("Allocate field elements - index {} ", index)),
                        &to_bytes_le![field_element].unwrap(),
                    )
                    .unwrap(),
                );
            }
            fe_bytes
        }
    }

    #[test]
    fn test_boolean_inputs_from_field_elements() {
        let rng = &mut test_rng();

        let mut cs = TestConstraintSystem::<Fr>::new();

        let mut field_elements = vec![];
        let mut field_element_gadgets = vec![];

        // Construct the field elements and field element gadgets
        for i in 0..1 {
            let field_element = Fr::rand(rng);
            let field_element_gadget =
                FpGadget::alloc(cs.ns(|| format!("field element_{}", i)), || Ok(field_element.clone())).unwrap();

            field_elements.push(field_element);
            field_element_gadgets.push(field_element_gadget);
        }

        // Construct expected field element bits

        let field_element_bytes = field_element_to_bytes(cs.ns(|| "field_element_to_bytes"), field_elements);

        let expected_fe_bits = field_element_bytes
            .iter()
            .enumerate()
            .flat_map(|(i, byte)| byte.to_bits_le(cs.ns(|| format!("to_bits_le_{}", i))))
            .collect::<Vec<_>>();

        // Construct gadget field element bits
        let fe_bits =
            BooleanInputGadget::<Fr, Fr>::from_field_elements(cs.ns(|| "from_field_elements"), &field_element_gadgets)
                .unwrap();

        for (i, (expected_bits, bits)) in expected_fe_bits.iter().zip(fe_bits.val.iter()).enumerate() {
            for (j, (expected_bit, bit)) in expected_bits.iter().zip(bits.iter()).enumerate() {
                expected_bit
                    .enforce_equal(cs.ns(|| format!("enforce_equal_bit_{}_{}", i, j)), bit)
                    .unwrap();
            }
        }

        assert!(cs.is_satisfied());
    }
}
