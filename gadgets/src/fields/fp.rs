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

use core::ops::Neg;
use std::borrow::Borrow;

use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{
    errors::SynthesisError,
    Assignment,
    ConstraintSystem,
    ConstraintVariable::{
        *,
        {self},
    },
    LinearCombination,
};
use snarkvm_utilities::{
    bititerator::{BitIteratorBE, BitIteratorLE},
    to_bytes_le,
    ToBytes,
};

use crate::{
    bits::{
        boolean::{AllocatedBit, Boolean},
        ToBitsBEGadget,
        ToBitsLEGadget,
        ToBytesBEGadget,
        ToBytesLEGadget,
    },
    integers::uint::UInt8,
    traits::{
        alloc::AllocGadget,
        eq::{ConditionalEqGadget, EqGadget, NEqGadget},
        fields::{FieldGadget, ToConstraintFieldGadget},
        select::{CondSelectGadget, ThreeBitCondNegLookupGadget, TwoBitLookupGadget},
    },
};

/// Represents a variable in the constraint system whose
/// value can be an arbitrary field element.
#[derive(Debug)]
pub struct AllocatedFp<F: PrimeField> {
    pub value: Option<F>,
    pub variable: ConstraintVariable<F>,
}

impl<F: PrimeField> AllocatedFp<F> {
    #[inline]
    pub fn from<CS: ConstraintSystem<F>>(mut cs: CS, value: &F) -> Self {
        Self::alloc(cs.ns(|| "from"), || Ok(*value)).unwrap()
    }
}

/// Represent variables corresponding to a field element in `F`.
#[derive(Clone, Debug)]
pub enum FpGadget<F: PrimeField> {
    /// Constant (not an allocated variable).
    Constant(F),

    /// Allocated variable in the constraint system.
    Variable(AllocatedFp<F>),
}

impl<F: PrimeField> From<AllocatedFp<F>> for FpGadget<F> {
    fn from(other: AllocatedFp<F>) -> Self {
        Self::Variable(other)
    }
}

impl<F: PrimeField> AllocatedFp<F> {
    /// Constructs `Self` from a `Boolean`: if `cond` is false, this outputs
    /// `zero`, else it outputs `one`.
    pub fn from_boolean<CS: ConstraintSystem<F>>(mut cs: CS, cond: Boolean) -> Result<Self, SynthesisError> {
        Ok(Self::alloc(cs.ns(|| ""), || {
            cond.get_value().and_then(|value| Some(F::from(value as u128))).get()
        })?)
    }

    #[inline]
    fn get_value(&self) -> Option<F> {
        self.value
    }

    #[inline]
    fn get_variable(&self) -> ConstraintVariable<F> {
        self.variable.clone()
    }

    #[inline]
    fn zero<CS: ConstraintSystem<F>>(_cs: CS) -> Self {
        let value = Some(F::zero());
        AllocatedFp {
            value,
            variable: ConstraintVariable::zero(),
        }
    }

    #[inline]
    fn one<CS: ConstraintSystem<F>>(_cs: CS) -> Self {
        let value = Some(F::one());
        AllocatedFp {
            value,
            variable: CS::one().into(),
        }
    }

    #[inline]
    fn conditionally_add_constant<CS: ConstraintSystem<F>>(&self, mut _cs: CS, bit: &Boolean, coeff: F) -> Self {
        let value = match (self.value, bit.get_value()) {
            (Some(v), Some(b)) => Some(if b { v + &coeff } else { v }),
            (..) => None,
        };
        AllocatedFp {
            value,
            variable: LC(bit.lc(CS::one(), coeff)) + &self.variable,
        }
    }

    #[inline]
    fn add<CS: ConstraintSystem<F>>(&self, mut _cs: CS, other: &Self) -> Self {
        let value = match (self.value, other.value) {
            (Some(val1), Some(val2)) => Some(val1 + &val2),
            (..) => None,
        };

        AllocatedFp {
            value,
            variable: &self.variable + &other.variable,
        }
    }

    fn double<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Self {
        let value = self.value.map(|val| val.double());
        let mut variable = self.variable.clone();
        variable.double_in_place();
        AllocatedFp { value, variable }
    }

    fn double_in_place<CS: ConstraintSystem<F>>(&mut self, _cs: CS) -> &mut Self {
        self.value.as_mut().map(|val| {
            val.double_in_place();
            val
        });
        self.variable.double_in_place();
        self
    }

    #[inline]
    fn sub<CS: ConstraintSystem<F>>(&self, mut _cs: CS, other: &Self) -> Self {
        let value = match (self.value, other.value) {
            (Some(val1), Some(val2)) => Some(val1 - &val2),
            (..) => None,
        };

        AllocatedFp {
            value,
            variable: &self.variable - &other.variable,
        }
    }

    #[inline]
    fn negate<CS: ConstraintSystem<F>>(&self, cs: CS) -> Self {
        let mut result = self.clone();
        result.negate_in_place(cs);
        result
    }

    #[inline]
    fn negate_in_place<CS: ConstraintSystem<F>>(&mut self, _cs: CS) -> &mut Self {
        if let Some(val) = self.value.as_mut() {
            *val = -(*val);
        }
        self.variable.negate_in_place();
        self
    }

    #[inline]
    fn mul<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        let product = Self::alloc(cs.ns(|| "mul"), || Ok(self.value.get()? * &other.value.get()?))?;
        cs.enforce(
            || "mul_constraint",
            |lc| &self.variable + lc,
            |lc| &other.variable + lc,
            |lc| &product.variable + lc,
        );
        Ok(product)
    }

    #[inline]
    fn add_constant<CS: ConstraintSystem<F>>(&self, _cs: CS, other: &F) -> Self {
        let value = self.value.map(|val| val + other);
        AllocatedFp {
            value,
            variable: self.variable.clone() + (*other, CS::one()),
        }
    }

    #[inline]
    #[allow(dead_code)]
    fn add_constant_in_place<CS: ConstraintSystem<F>>(&mut self, _cs: CS, other: &F) -> &mut Self {
        if let Some(val) = self.value.as_mut() {
            *val += other;
        }
        self.variable += (*other, CS::one());
        self
    }

    /// Output `self - other`
    ///
    /// This does not create any constraints.
    fn sub_constant<CS: ConstraintSystem<F>>(&self, _cs: CS, other: &F) -> Self {
        self.add_constant(_cs, &other.neg())
    }

    #[inline]
    fn mul_by_constant<CS: ConstraintSystem<F>>(&self, cs: CS, other: &F) -> Self {
        let mut result = self.clone();
        result.mul_by_constant_in_place(cs, other);
        result
    }

    #[inline]
    fn mul_by_constant_in_place<CS: ConstraintSystem<F>>(&mut self, mut _cs: CS, other: &F) -> &mut Self {
        if let Some(val) = self.value.as_mut() {
            *val *= other;
        }
        self.variable *= *other;
        self
    }

    #[inline]
    fn inverse<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Self, SynthesisError> {
        let inverse = Self::alloc(cs.ns(|| "inverse"), || {
            let result = self.value.get()?;
            let inv = result.inverse().expect("Inverse doesn't exist!");
            Ok(inv)
        })?;

        let one = CS::one();
        cs.enforce(
            || "inv_constraint",
            |lc| &self.variable + lc,
            |lc| &inverse.variable + lc,
            |lc| lc + one,
        );
        Ok(inverse)
    }

    fn frobenius_map<CS: ConstraintSystem<F>>(&self, _: CS, _: usize) -> Self {
        self.clone()
    }

    #[allow(dead_code)]
    fn frobenius_map_in_place<CS: ConstraintSystem<F>>(&mut self, _: CS, _: usize) -> &mut Self {
        self
    }

    fn mul_equals<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self, result: &Self) {
        cs.enforce(
            || "mul_constraint",
            |lc| &self.variable + lc,
            |lc| &other.variable + lc,
            |lc| &result.variable + lc,
        );
    }

    fn square_equals<CS: ConstraintSystem<F>>(&self, mut cs: CS, result: &Self) {
        cs.enforce(
            || "sqr_constraint",
            |lc| &self.variable + lc,
            |lc| &self.variable + lc,
            |lc| &result.variable + lc,
        );
    }

    /// Outputs the bit `self != other`.
    ///
    /// This requires three constraints.
    pub fn is_neq<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        let is_not_equal = Boolean::alloc(cs.ns(|| "alloc_is_not_equal"), || {
            Ok(self.value.get()? != other.value.get()?)
        })?;
        let multiplier = cs.alloc(
            || "muliplier",
            || {
                if is_not_equal.get_value().get()? {
                    (self.value.get()? - &other.value.get()?).inverse().get()
                } else {
                    Ok(F::one())
                }
            },
        )?;

        // Completeness:
        // Case 1: self != other:
        // ----------------------
        //   constraint 1:
        //   (self - other) * multiplier = is_not_equal
        //   => (non_zero) * multiplier = 1 (satisfied, because multiplier = 1/(self -
        // other)
        //
        //   constraint 2:
        //   (self - other) * not(is_not_equal) = 0
        //   => (non_zero) * not(1) = 0
        //   => (non_zero) * 0 = 0
        //
        // Case 2: self == other:
        // ----------------------
        //   constraint 1:
        //   (self - other) * multiplier = is_not_equal
        //   => 0 * multiplier = 0 (satisfied, because multiplier = 1
        //
        //   constraint 2:
        //   (self - other) * not(is_not_equal) = 0
        //   => 0 * not(0) = 0
        //   => 0 * 1 = 0
        //
        // --------------------------------------------------------------------
        //
        // Soundness:
        // Case 1: self != other, but is_not_equal = 0.
        // --------------------------------------------
        //   constraint 1:
        //   (self - other) * multiplier = is_not_equal
        //   => non_zero * multiplier = 0 (only satisfiable if multiplier == 0)
        //
        //   constraint 2:
        //   (self - other) * not(is_not_equal) = 0
        //   => (non_zero) * 1 = 0 (impossible)
        //
        // Case 2: self == other, but is_not_equal = 1.
        // --------------------------------------------
        //   constraint 1:
        //   (self - other) * multiplier = is_not_equal
        //   0 * multiplier = 1 (unsatisfiable)

        let one = CS::one();
        cs.enforce(
            || "case_1",
            |lc| &self.variable - &other.variable + lc,
            |lc| lc + multiplier,
            |_lc| is_not_equal.lc(one, F::one()),
        );

        cs.enforce(
            || "case_2",
            |lc| &self.variable - &other.variable + lc,
            |_lc| is_not_equal.not().lc(one, F::one()),
            |lc| lc,
        );

        Ok(is_not_equal)
    }

    #[allow(dead_code)]
    fn cost_of_mul() -> usize {
        1
    }

    #[allow(dead_code)]
    fn cost_of_inv() -> usize {
        1
    }
}

impl<F: PrimeField> PartialEq for AllocatedFp<F> {
    fn eq(&self, other: &Self) -> bool {
        self.value.is_some() && self.value == other.value
    }
}

impl<F: PrimeField> Eq for AllocatedFp<F> {}

impl<F: PrimeField> EqGadget<F> for AllocatedFp<F> {
    fn is_eq<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        Ok(self.is_neq(cs, other)?.not())
    }
}

impl<F: PrimeField> ConditionalEqGadget<F> for AllocatedFp<F> {
    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        let difference = self.sub(cs.ns(|| "difference"), other);
        let one = CS::one();
        let one_const = F::one();
        cs.enforce(
            || "conditional_equals",
            |lc| &difference.variable + lc,
            |lc| lc + &condition.lc(one, one_const),
            |lc| lc,
        );
        Ok(())
    }

    fn cost() -> usize {
        1
    }
}

impl<F: PrimeField> NEqGadget<F> for AllocatedFp<F> {
    #[inline]
    fn enforce_not_equal<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<(), SynthesisError> {
        let a_minus_b = self.sub(cs.ns(|| "A - B"), other);
        a_minus_b.inverse(cs.ns(|| "Enforce inverse exists"))?;
        Ok(())
    }

    fn cost() -> usize {
        1
    }
}

impl<F: PrimeField> ToBitsBEGadget<F> for AllocatedFp<F> {
    /// Outputs the binary representation of the value in `self` in *big-endian*
    /// form.
    fn to_bits_be<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let num_bits = F::Parameters::MODULUS_BITS;
        let bit_values = match self.value {
            Some(value) => {
                let mut field_char = BitIteratorBE::new(F::characteristic());
                let mut tmp = Vec::with_capacity(num_bits as usize);
                let mut found_one = false;
                for b in BitIteratorBE::new(value.to_repr()) {
                    // Skip leading bits
                    found_one |= field_char.next().unwrap();
                    if !found_one {
                        continue;
                    }

                    tmp.push(Some(b));
                }

                assert_eq!(tmp.len(), num_bits as usize);

                tmp
            }
            None => vec![None; num_bits as usize],
        };

        let mut bits = Vec::with_capacity(bit_values.len());
        for (i, b) in bit_values.into_iter().enumerate() {
            bits.push(AllocatedBit::alloc(cs.ns(|| format!("bit {}", i)), || b.get())?);
        }

        let mut lc = LinearCombination::zero();
        let mut coeff = F::one();

        for bit in bits.iter().rev() {
            lc += (coeff, bit.get_variable());

            coeff.double_in_place();
        }

        lc = &self.variable - lc;

        cs.enforce(|| "unpacking_constraint", |lc| lc, |lc| lc, |_| lc);

        Ok(bits.into_iter().map(Boolean::from).collect())
    }

    fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let bits = self.to_bits_be(&mut cs)?;
        Boolean::enforce_in_field::<_, _, F>(&mut cs, &bits)?;
        Ok(bits)
    }
}

impl<F: PrimeField> ToBitsLEGadget<F> for AllocatedFp<F> {
    /// Outputs the binary representation of the value in `self` in *little-endian*
    /// form.
    fn to_bits_le<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let num_bits = F::Parameters::MODULUS_BITS;
        let mut bit_values = match self.value {
            Some(value) => {
                let field_char = BitIteratorBE::new(F::characteristic());
                let bits: Vec<_> = BitIteratorBE::new(value.to_repr())
                    .zip(field_char)
                    .skip_while(|(_, c)| !*c)
                    .map(|(b, _)| Some(b))
                    .collect();
                assert_eq!(bits.len(), num_bits as usize);
                bits
            }
            None => vec![None; num_bits as usize],
        };

        // Convert to little-endian
        bit_values.reverse();

        let bits: Vec<_> = bit_values
            .into_iter()
            .enumerate()
            .map(|(i, b)| Boolean::alloc(cs.ns(|| format!("bit {}", i)), || b.get()))
            .collect::<Result<_, _>>()?;

        let mut lc = LinearCombination::zero();
        let mut coeff = F::one();

        for bit in bits.iter() {
            lc = &lc + bit.lc(CS::one(), F::one()) * coeff;

            coeff.double_in_place();
        }

        lc = &self.variable.clone().neg() + lc;

        cs.enforce(|| "unpacking_constraint", |lc| lc, |lc| lc, |_| lc);

        Ok(bits.into_iter().map(Boolean::from).collect())
    }

    fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let bits = self.to_bits_le(&mut cs)?;

        Boolean::enforce_in_field_le::<F, _>(&mut cs, &bits)?;
        Ok(bits)
    }
}

impl<F: PrimeField> ToBytesLEGadget<F> for AllocatedFp<F> {
    fn to_bytes_le<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let byte_values = match self.value {
            Some(value) => to_bytes_le![&value.to_repr()]?
                .into_iter()
                .map(Some)
                .collect::<Vec<_>>(),
            None => {
                let default = F::default();
                let default_len = to_bytes_le![&default].unwrap().len();
                vec![None; default_len]
            }
        };

        let bytes = UInt8::alloc_vec(cs.ns(|| "Alloc bytes"), &byte_values)?;

        let mut lc = LinearCombination::zero();
        let mut coeff = F::one();

        for bit in bytes.iter().flat_map(|byte_gadget| byte_gadget.bits.clone()) {
            match bit {
                Boolean::Is(bit) => {
                    lc += (coeff, bit.get_variable());
                    coeff.double_in_place();
                }
                Boolean::Constant(_) | Boolean::Not(_) => unreachable!(),
            }
        }

        lc = &self.variable - lc;

        cs.enforce(|| "unpacking_constraint", |lc| lc, |lc| lc, |_| lc);

        Ok(bytes)
    }

    fn to_bytes_le_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let bytes = self.to_bytes_le(&mut cs)?;
        Boolean::enforce_in_field::<_, _, F>(
            &mut cs,
            &bytes
                .iter()
                .flat_map(|byte_gadget| byte_gadget.u8_to_bits_le())
                // This reverse maps the bits into big-endian form, as required by `enforce_in_field`.
                .rev()
                .collect::<Vec<_>>(),
        )?;

        Ok(bytes)
    }
}

impl<F: PrimeField> ToBytesBEGadget<F> for AllocatedFp<F> {
    fn to_bytes_be<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut bytes = self.to_bytes_le(cs)?;
        bytes.reverse();
        Ok(bytes)
    }

    fn to_bytes_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut bytes = self.to_bytes_le_strict(cs)?;
        bytes.reverse();
        Ok(bytes)
    }
}

impl<F: PrimeField> CondSelectGadget<F> for AllocatedFp<F> {
    #[inline]
    fn conditionally_select<CS: ConstraintSystem<F>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        if let Boolean::Constant(cond) = *cond {
            if cond { Ok(first.clone()) } else { Ok(second.clone()) }
        } else {
            let result = Self::alloc(cs.ns(|| ""), || {
                cond.get_value()
                    .and_then(|cond| if cond { first } else { second }.get_value())
                    .get()
            })?;
            // a = self; b = other; c = cond;
            //
            // r = c * a + (1  - c) * b
            // r = b + c * (a - b)
            // c * (a - b) = r - b
            let one = CS::one();
            cs.enforce(
                || "conditionally_select",
                |_| cond.lc(one, F::one()),
                |lc| (&first.variable - &second.variable) + lc,
                |lc| (&result.variable - &second.variable) + lc,
            );

            Ok(result)
        }
    }

    fn cost() -> usize {
        1
    }
}

/// Uses two bits to perform a lookup into a table
/// `b` is little-endian: `b[0]` is LSB.
impl<F: PrimeField> TwoBitLookupGadget<F> for AllocatedFp<F> {
    type TableConstant = F;

    fn two_bit_lookup<CS: ConstraintSystem<F>>(
        mut cs: CS,
        b: &[Boolean],
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(b.len() == 2);
        debug_assert!(c.len() == 4);

        let result = Self::alloc(cs.ns(|| "Allocate lookup result"), || {
            match (b[0].get_value().get()?, b[1].get_value().get()?) {
                (false, false) => Ok(c[0]),
                (false, true) => Ok(c[2]),
                (true, false) => Ok(c[1]),
                (true, true) => Ok(c[3]),
            }
        })?;
        let one = CS::one();
        cs.enforce(
            || "Enforce lookup",
            |lc| lc + b[1].lc(one, c[3] - &c[2] - &c[1] + &c[0]) + (c[1] - &c[0], one),
            |lc| lc + b[0].lc(one, F::one()),
            |lc| result.get_variable() + lc + (-c[0], one) + b[1].lc(one, c[0] - &c[2]),
        );

        Ok(result)
    }

    fn cost() -> usize {
        1
    }
}

impl<F: PrimeField> ThreeBitCondNegLookupGadget<F> for AllocatedFp<F> {
    type TableConstant = F;

    fn three_bit_cond_neg_lookup<CS: ConstraintSystem<F>>(
        mut cs: CS,
        b: &[Boolean],
        b0b1: &Boolean,
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(b.len() == 3);
        debug_assert!(c.len() == 4);

        let result = Self::alloc(cs.ns(|| "Allocate lookup result"), || {
            let y = match (b[0].get_value().get()?, b[1].get_value().get()?) {
                (false, false) => c[0],
                (false, true) => c[2],
                (true, false) => c[1],
                (true, true) => c[3],
            };
            if b[2].get_value().get()? { Ok(-y) } else { Ok(y) }
        })?;

        let one = CS::one();
        let y_lc = b0b1.lc(one, c[3] - &c[2] - &c[1] + &c[0])
            + b[0].lc(one, c[1] - &c[0])
            + b[1].lc(one, c[2] - &c[0])
            + (c[0], one);
        cs.enforce(
            || "Enforce lookup",
            |_| y_lc.clone() + y_lc.clone(),
            |lc| lc + b[2].lc(one, F::one()),
            |_| -result.get_variable() + y_lc.clone(),
        );

        Ok(result)
    }

    fn cost() -> usize {
        2
    }
}

impl<F: PrimeField> Clone for AllocatedFp<F> {
    fn clone(&self) -> Self {
        Self {
            value: self.value,
            variable: self.variable.clone(),
        }
    }
}

impl<F: PrimeField> AllocGadget<F, F> for AllocatedFp<F> {
    #[inline]
    fn alloc_constant<FN, T, CS: ConstraintSystem<F>>(cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<F>,
    {
        // TODO (raychu86): Alloc a constant.
        Self::alloc(cs, value_gen)
    }

    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<F>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<F>,
    {
        let mut value = None;
        let variable = cs.alloc(
            || "alloc",
            || {
                let tmp = *value_gen()?.borrow();
                value = Some(tmp);
                Ok(tmp)
            },
        )?;
        Ok(AllocatedFp {
            value,
            variable: Var(variable),
        })
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<F>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<F>,
    {
        let mut value = None;
        let variable = cs.alloc_input(
            || "alloc",
            || {
                let tmp = *value_gen()?.borrow();
                value = Some(tmp);
                Ok(tmp)
            },
        )?;
        Ok(AllocatedFp {
            value,
            variable: Var(variable),
        })
    }
}

impl<F: PrimeField> ToConstraintFieldGadget<F> for AllocatedFp<F> {
    fn to_constraint_field<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<FpGadget<F>>, SynthesisError> {
        Ok(vec![self.clone().into()])
    }
}

// FpGadget Impl

impl<F: PrimeField> FpGadget<F> {
    /// Constructs `Self` from a `Boolean`: if `other` is false, this outputs
    /// `zero`, else it outputs `one`.
    pub fn from_boolean<CS: ConstraintSystem<F>>(cs: CS, other: Boolean) -> Result<Self, SynthesisError> {
        if let Boolean::Constant(b) = other {
            Ok(Self::Constant(F::from(b as u128)))
        } else {
            Ok(Self::Variable(AllocatedFp::from_boolean(cs, other)?))
        }
    }
}

impl<F: PrimeField> FieldGadget<F, F> for FpGadget<F> {
    type Variable = ConstraintVariable<F>;

    #[inline]
    fn get_value(&self) -> Option<F> {
        match self {
            FpGadget::Constant(v) => Some(*v),
            FpGadget::Variable(v) => v.value,
        }
    }

    // TODO (raychu86): Fix the case where FpGadget is constant.
    #[inline]
    fn get_variable(&self) -> <Self as FieldGadget<F, F>>::Variable {
        match self {
            FpGadget::Constant(_v) => unimplemented!(),
            FpGadget::Variable(v) => v.variable.clone(),
        }
    }

    #[inline]
    fn zero<CS: ConstraintSystem<F>>(_cs: CS) -> Result<Self, SynthesisError> {
        //TODO (raychu86): Use constant constraint optimization.
        // Ok(Self::Constant(F::zero()))

        Ok(Self::Variable(AllocatedFp::zero(_cs)))
    }

    #[inline]
    fn one<CS: ConstraintSystem<F>>(_cs: CS) -> Result<Self, SynthesisError> {
        //TODO (raychu86): Use constant constraint optimization.
        // Ok(Self::Constant(F::one()))

        Ok(Self::Variable(AllocatedFp::one(_cs)))
    }

    #[inline]
    fn conditionally_add_constant<CS: ConstraintSystem<F>>(
        &self,
        mut _cs: CS,
        bit: &Boolean,
        coeff: F,
    ) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => {
                let value = match bit.get_value() {
                    Some(b) => {
                        if b {
                            *c + &coeff
                        } else {
                            *c
                        }
                    }
                    _ => *c,
                };
                Ok(Self::Constant(value))
            }
            Self::Variable(v) => Ok(Self::Variable(v.conditionally_add_constant(_cs, bit, coeff))),
        }
    }

    #[inline]
    fn add<CS: ConstraintSystem<F>>(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => Ok(Self::Constant(*c1 + &*c2)),
            (Self::Constant(c), Self::Variable(v)) | (Self::Variable(v), Self::Constant(c)) => {
                Ok(Self::Variable(v.add_constant(cs, &*c)))
            }
            (Self::Variable(v1), Self::Variable(v2)) => Ok(Self::Variable(v1.add(cs, v2))),
        }
    }

    fn double<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(c.double())),
            Self::Variable(v) => Ok(Self::Variable(v.double(_cs))),
        }
    }

    fn double_in_place<CS: ConstraintSystem<F>>(&mut self, _cs: CS) -> Result<&mut Self, SynthesisError> {
        match self {
            Self::Constant(c) => {
                c.double_in_place();
            }
            Self::Variable(v) => {
                v.double_in_place(_cs);
            }
        }

        Ok(self)
    }

    #[inline]
    fn sub<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => Ok(Self::Constant(*c1 - &*c2)),
            (Self::Variable(v), Self::Constant(c)) => Ok(Self::Variable(v.sub_constant(cs.ns(|| "sub_constant"), &*c))),
            (Self::Constant(c), Self::Variable(v)) => Ok(Self::Variable(
                v.sub_constant(cs.ns(|| "sub_constant"), &*c).negate(cs.ns(|| "negate")),
            )),
            (Self::Variable(v1), Self::Variable(v2)) => Ok(Self::Variable(v1.sub(cs.ns(|| "sub"), v2))),
        }
    }

    #[inline]
    fn negate<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(-*c)),
            Self::Variable(v) => Ok(Self::Variable(v.negate(cs))),
        }
    }

    #[inline]
    fn negate_in_place<CS: ConstraintSystem<F>>(&mut self, _cs: CS) -> Result<&mut Self, SynthesisError> {
        match self {
            Self::Constant(c) => {
                *c = c.neg();
            }
            Self::Variable(v) => {
                v.negate_in_place(_cs);
            }
        }

        Ok(self)
    }

    #[inline]
    fn mul<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => Ok(Self::Constant(*c1 * &*c2)),
            (Self::Variable(v), Self::Constant(c)) | (Self::Constant(c), Self::Variable(v)) => {
                Ok(Self::Variable(v.mul_by_constant(cs.ns(|| "mul_by_constant"), &*c)))
            }
            (Self::Variable(v1), Self::Variable(v2)) => Ok(Self::Variable(v1.mul(cs.ns(|| "mul"), v2)?)),
        }
    }

    #[inline]
    fn add_constant<CS: ConstraintSystem<F>>(&self, _cs: CS, other: &F) -> Result<Self, SynthesisError> {
        self.add(_cs, &Self::Constant(*other))
    }

    #[inline]
    fn add_constant_in_place<CS: ConstraintSystem<F>>(
        &mut self,
        _cs: CS,
        other: &F,
    ) -> Result<&mut Self, SynthesisError> {
        *self = self.add_constant(_cs, other)?;
        Ok(self)
    }

    #[inline]
    fn mul_by_constant<CS: ConstraintSystem<F>>(&self, cs: CS, other: &F) -> Result<Self, SynthesisError> {
        self.mul(cs, &Self::Constant(*other))
    }

    #[inline]
    fn mul_by_constant_in_place<CS: ConstraintSystem<F>>(
        &mut self,
        mut _cs: CS,
        other: &F,
    ) -> Result<&mut Self, SynthesisError> {
        *self = self.mul_by_constant(_cs, other)?;
        Ok(self)
    }

    #[inline]
    fn inverse<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(f) => f.inverse().get().map(Self::Constant),
            Self::Variable(v) => v.inverse(cs).map(Self::Variable),
        }
    }

    fn frobenius_map<CS: ConstraintSystem<F>>(&self, _cs: CS, _power: usize) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(f) => {
                let mut f = *f;
                f.frobenius_map(_power);
                Ok(FpGadget::Constant(f))
            }
            Self::Variable(v) => Ok(Self::Variable(v.frobenius_map(_cs, _power))),
        }
    }

    fn frobenius_map_in_place<CS: ConstraintSystem<F>>(
        &mut self,
        _cs: CS,
        _power: usize,
    ) -> Result<&mut Self, SynthesisError> {
        *self = self.frobenius_map(_cs, _power)?;
        Ok(self)
    }

    fn mul_equals<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        result: &Self,
    ) -> Result<(), SynthesisError> {
        match (self, other, result) {
            (Self::Constant(_), Self::Constant(_), Self::Constant(_)) => Ok(()),
            (Self::Constant(_), Self::Constant(_), _)
            | (Self::Constant(_), Self::Variable(_), _)
            | (Self::Variable(_), Self::Constant(_), _) => {
                let mul_other = self.mul(cs.ns(|| "mul"), other)?;
                result.enforce_equal(cs.ns(|| "encorce_equal"), &mul_other)
            } // this multiplication should be free
            (Self::Variable(v1), Self::Variable(v2), Self::Variable(v3)) => {
                v1.mul_equals(cs.ns(|| "mul_equals"), v2, v3);
                Ok(())
            }
            (Self::Variable(v1), Self::Variable(v2), Self::Constant(f)) => {
                let v3 = AllocatedFp::alloc(cs.ns(|| "alloc_constant"), || Ok(f)).unwrap();
                v1.mul_equals(cs, v2, &v3);
                Ok(())
            }
        }
    }

    fn square_equals<CS: ConstraintSystem<F>>(&self, mut cs: CS, result: &Self) -> Result<(), SynthesisError> {
        match (self, result) {
            (Self::Constant(_), Self::Constant(_)) => Ok(()),
            (Self::Constant(f), Self::Variable(r)) => {
                let v = AllocatedFp::alloc(cs.ns(|| "alloc_v"), || Ok(f))?;
                v.square_equals(cs, &r);
                Ok(())
            }
            (Self::Variable(v), Self::Constant(f)) => {
                let r = AllocatedFp::alloc(cs.ns(|| "alloc_v"), || Ok(f))?;
                v.square_equals(cs, &r);
                Ok(())
            }
            (Self::Variable(v1), Self::Variable(v2)) => {
                v1.square_equals(cs, v2);
                Ok(())
            }
        }
    }

    fn cost_of_mul() -> usize {
        1
    }

    fn cost_of_inv() -> usize {
        1
    }
}

impl<F: PrimeField> PartialEq for FpGadget<F> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Constant(v1), Self::Constant(v2)) => v1.eq(v2),
            (Self::Constant(c), Self::Variable(v)) | (Self::Variable(v), Self::Constant(c)) => {
                v.value.is_some() && v.value == Some(*c)
            }
            (Self::Variable(v1), Self::Variable(v2)) => v1.eq(v2),
        }
    }
}

impl<F: PrimeField> Eq for FpGadget<F> {}

impl<F: PrimeField> EqGadget<F> for FpGadget<F> {
    fn is_eq<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => Ok(Boolean::Constant(c1 == c2)),
            (Self::Constant(c), Self::Variable(v)) | (Self::Variable(v), Self::Constant(c)) => {
                let c = AllocatedFp::alloc_constant(cs.ns(|| "alloc_fp_constant"), || Ok(c))?;
                c.is_eq(cs.ns(|| "is_eq"), v)
            }
            (Self::Variable(v1), Self::Variable(v2)) => v1.is_eq(cs.ns(|| "is_eq"), v2),
        }
    }
}

impl<F: PrimeField> ConditionalEqGadget<F> for FpGadget<F> {
    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        match (self, other) {
            (Self::Constant(_), Self::Constant(_)) => Ok(()),
            (Self::Variable(v), Self::Constant(c)) => {
                let c = AllocatedFp::alloc_constant(cs.ns(|| "alloc_constant"), || Ok(c))?;
                c.conditional_enforce_equal(cs, v, condition)
            }
            (Self::Constant(c), Self::Variable(v)) => {
                let c = AllocatedFp::alloc_constant(cs.ns(|| "alloc_constant"), || Ok(c))?;
                c.conditional_enforce_equal(cs, v, condition)
            }
            (Self::Variable(v1), Self::Variable(v2)) => v1.conditional_enforce_equal(cs, v2, condition),
        }
    }

    fn cost() -> usize {
        1
    }
}

impl<F: PrimeField> NEqGadget<F> for FpGadget<F> {
    #[inline]
    fn enforce_not_equal<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<(), SynthesisError> {
        match (self, other) {
            (Self::Constant(_), Self::Constant(_)) => Ok(()),
            (Self::Constant(c), Self::Variable(v)) | (Self::Variable(v), Self::Constant(c)) => {
                let c = AllocatedFp::alloc_constant(cs.ns(|| "alloc_constant"), || Ok(c))?; // change to alloc_constant
                c.enforce_not_equal(cs, v)
            }
            (Self::Variable(v1), Self::Variable(v2)) => v1.enforce_not_equal(cs, v2),
        }
    }

    fn cost() -> usize {
        1
    }
}

impl<F: PrimeField> ToBitsBEGadget<F> for FpGadget<F> {
    /// Outputs the binary representation of the value in `self` in *big-endian*
    /// form.
    fn to_bits_be<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        match self {
            Self::Constant(_) => self.to_bits_be_strict(cs),
            Self::Variable(v) => v.to_bits_be(cs),
        }
    }

    fn to_bits_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(BitIteratorBE::new(&c.to_repr())
                .take((F::Parameters::MODULUS_BITS) as usize)
                .map(Boolean::constant)
                .collect::<Vec<_>>()),
            Self::Variable(v) => v.to_bits_be_strict(cs),
        }
    }
}

impl<F: PrimeField> ToBitsLEGadget<F> for FpGadget<F> {
    /// Outputs the binary representation of the value in `self` in *little-endian*
    /// form.
    fn to_bits_le<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        match self {
            Self::Constant(_) => self.to_bits_le_strict(cs),
            Self::Variable(v) => v.to_bits_le(cs),
        }
    }

    fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(BitIteratorLE::new(&c.to_repr())
                .take((F::Parameters::MODULUS_BITS) as usize)
                .map(Boolean::constant)
                .collect::<Vec<_>>()),
            Self::Variable(v) => v.to_bits_le_strict(cs),
        }
    }
}

impl<F: PrimeField> ToBytesLEGadget<F> for FpGadget<F> {
    fn to_bytes_le<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(&to_bytes_le![c].unwrap())),
            Self::Variable(v) => v.to_bytes_le(cs),
        }
    }

    fn to_bytes_le_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(&to_bytes_le![c].unwrap())),
            Self::Variable(v) => v.to_bytes_le_strict(cs),
        }
    }
}

impl<F: PrimeField> ToBytesBEGadget<F> for FpGadget<F> {
    fn to_bytes_be<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        match self {
            Self::Constant(c) => {
                let bytes = &to_bytes_le![c].unwrap().into_iter().rev().collect::<Vec<u8>>();
                Ok(UInt8::constant_vec(bytes))
            }
            Self::Variable(v) => v.to_bytes_be(cs),
        }
    }

    fn to_bytes_be_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        match self {
            Self::Constant(c) => {
                let bytes = &to_bytes_le![c].unwrap().into_iter().rev().collect::<Vec<u8>>();
                Ok(UInt8::constant_vec(bytes))
            }
            Self::Variable(v) => v.to_bytes_be_strict(cs),
        }
    }
}

impl<F: PrimeField> CondSelectGadget<F> for FpGadget<F> {
    /// Conditionally selects one of `first` and `second` based on the value of
    /// `self`:
    ///
    /// If `cond` is `true`, this outputs `first`; else, it outputs `second`.
    #[inline]
    fn conditionally_select<CS: ConstraintSystem<F>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        match cond {
            Boolean::Constant(true) => Ok(first.clone()),
            Boolean::Constant(false) => Ok(second.clone()),
            _ => {
                match (first, second) {
                    (Self::Constant(t), Self::Constant(f)) => {
                        let is = AllocatedFp::from_boolean(cs.ns(|| "from_bool_is"), *cond)?;
                        let not = AllocatedFp::from_boolean(cs.ns(|| "from_bool_not"), cond.not())?;
                        // cond * t + (1 - cond) * f
                        let not_f = &not.mul_by_constant(cs.ns(|| "mul_by_f"), &*f);
                        Ok(is
                            .mul_by_constant(cs.ns(|| "mul_by_t"), &*t)
                            .add(cs.ns(|| "add"), &not_f)
                            .into())
                    }
                    (..) => {
                        let first = match first {
                            Self::Constant(f) => {
                                AllocatedFp::alloc_constant(cs.ns(|| "alloc_constant_first"), || Ok(f))?
                            }
                            Self::Variable(v) => v.clone(),
                        };
                        let second = match second {
                            Self::Constant(f) => {
                                AllocatedFp::alloc_constant(cs.ns(|| "alloc_constant_second"), || Ok(f))?
                            }
                            Self::Variable(v) => v.clone(),
                        };
                        AllocatedFp::conditionally_select(cs.ns(|| "conditionally_select"), &cond, &first, &second)
                            .map(Self::Variable)
                    }
                }
            }
        }
    }

    fn cost() -> usize {
        1
    }
}

/// Uses two bits to perform a lookup into a table
/// `b` is little-endian: `b[0]` is LSB.
impl<F: PrimeField> TwoBitLookupGadget<F> for FpGadget<F> {
    type TableConstant = F;

    fn two_bit_lookup<CS: ConstraintSystem<F>>(
        cs: CS,
        b: &[Boolean],
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(b.len() == 2);
        debug_assert!(c.len() == 4);

        //TODO (raychu86): Use constant constraint optimization.

        // // Check if the inputs are constant
        // let mut constant = true;
        // for bit in b {
        //     match bit {
        //         Boolean::Constant(_) => {}
        //         _ => constant = false,
        //     }
        // }
        //
        // if constant {
        //     let lsb = usize::from(b[0].get_value().get()?);
        //     let msb = usize::from(b[1].get_value().get()?);
        //     let index = lsb + (msb << 1);
        //     println!("two-bit-lookup");
        //     Ok(Self::Constant(c[index]))
        // } else {
        //     AllocatedFp::two_bit_lookup(cs, b, c).map(Self::Variable)
        // }

        AllocatedFp::two_bit_lookup(cs, b, c).map(Self::Variable)
    }

    fn cost() -> usize {
        1
    }
}

impl<F: PrimeField> ThreeBitCondNegLookupGadget<F> for FpGadget<F> {
    type TableConstant = F;

    fn three_bit_cond_neg_lookup<CS: ConstraintSystem<F>>(
        cs: CS,
        b: &[Boolean],
        b0b1: &Boolean,
        c: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert_eq!(b.len(), 3);
        debug_assert_eq!(c.len(), 4);

        //TODO (raychu86): Use constant constraint optimization.

        // // Chck if the inputs are constant
        // let mut constant = true;
        // for bit in b {
        //     match bit {
        //         Boolean::Constant(_) => {}
        //         _ => constant = false,
        //     }
        // }
        //
        // match b0b1 {
        //     Boolean::Constant(_) => {}
        //     _ => constant = false,
        // }
        //
        // if constant {
        //     // We only have constants
        //
        //     let lsb = usize::from(b[0].get_value().get()?);
        //     let msb = usize::from(b[1].get_value().get()?);
        //     let index = lsb + (msb << 1);
        //     let intermediate = c[index];
        //
        //     let is_negative = b[2].get_value().get()?;
        //     let y = if is_negative { -intermediate } else { intermediate };
        //
        //     println!("three-bit-cond-neg-lookup");
        //
        //     Ok(Self::Constant(y))
        // } else {
        //     AllocatedFp::three_bit_cond_neg_lookup(cs, b, b0b1, c).map(Self::Variable)
        // }

        AllocatedFp::three_bit_cond_neg_lookup(cs, b, b0b1, c).map(Self::Variable)
    }

    fn cost() -> usize {
        2
    }
}

impl<F: PrimeField> AllocGadget<F, F> for FpGadget<F> {
    #[inline]
    fn alloc_constant<FN, T, CS: ConstraintSystem<F>>(_cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<F>,
    {
        Ok(Self::Constant(*value_gen()?.borrow()))
    }

    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<F>>(cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<F>,
    {
        AllocatedFp::alloc(cs, value_gen).map(Self::Variable)
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<F>>(cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<F>,
    {
        AllocatedFp::alloc_input(cs, value_gen).map(Self::Variable)
    }
}

impl<F: PrimeField> ToConstraintFieldGadget<F> for FpGadget<F> {
    fn to_constraint_field<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<FpGadget<F>>, SynthesisError> {
        Ok(vec![self.clone()])
    }
}
