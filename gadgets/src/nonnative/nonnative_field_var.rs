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

use std::{
    borrow::Borrow,
    hash::{Hash, Hasher},
};

use crate::{
    bits::{Boolean, ToBitsBEGadget, ToBitsLEGadget, ToBytesBEGadget, ToBytesLEGadget},
    integers::uint::UInt8,
    traits::{
        alloc::AllocGadget,
        eq::{ConditionalEqGadget, EqGadget, NEqGadget},
        fields::FieldGadget,
        select::{CondSelectGadget, ThreeBitCondNegLookupGadget, TwoBitLookupGadget},
    },
};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, Assignment, ConstraintSystem};
use snarkvm_utilities::{
    bititerator::{BitIteratorBE, BitIteratorLE},
    to_bytes_le,
    ToBytes,
};

use crate::nonnative::{AllocatedNonNativeFieldVar, NonNativeFieldMulResultVar};

/// A gadget for representing non-native (`TargetField`) field elements over the constraint field (`BaseField`).
#[derive(Clone, Debug)]
pub enum NonNativeFieldVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// Constant
    Constant(TargetField),
    /// Allocated gadget
    Var(AllocatedNonNativeFieldVar<TargetField, BaseField>),
}

impl<TargetField: PrimeField, BaseField: PrimeField> PartialEq for NonNativeFieldVar<TargetField, BaseField> {
    fn eq(&self, other: &Self) -> bool {
        self.value().unwrap_or_default().eq(&other.value().unwrap_or_default())
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> Eq for NonNativeFieldVar<TargetField, BaseField> {}

impl<TargetField: PrimeField, BaseField: PrimeField> Hash for NonNativeFieldVar<TargetField, BaseField> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value().unwrap_or_default().hash(state);
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> NonNativeFieldVar<TargetField, BaseField> {
    /// Get the value of the gadget.
    pub fn value(&self) -> Result<TargetField, SynthesisError> {
        match self {
            Self::Constant(v) => Ok(*v),
            Self::Var(v) => v.value(),
        }
    }

    /// Constructs `Self` from a `Boolean`: if `boolean` is `true`, this outputs
    /// `one`, else it outputs `zero`.
    pub fn from_boolean<CS: ConstraintSystem<BaseField>>(cs: CS, boolean: Boolean) -> Result<Self, SynthesisError> {
        if let Boolean::Constant(b) = boolean {
            Ok(Self::Constant(<TargetField as From<u128>>::from(b as u128)))
        } else {
            // `other` is a variable
            let one = Self::Constant(TargetField::one());
            let zero = Self::Constant(TargetField::zero());
            Self::conditionally_select(cs, &boolean, &one, &zero)
        }
    }

    /// Determine if two `NonNativeFieldVar` instances are equal.
    pub fn is_eq<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        let mut constant = true;

        if let Self::Constant(_) = self {
            constant = false;
        }

        if let Self::Constant(_) = other {
            constant = false;
        }

        if constant {
            Ok(Boolean::Constant(self.value()? == other.value()?))
        } else {
            let should_enforce_equal = Boolean::alloc(cs.ns(|| "alloc"), || Ok(self.value()? == other.value()?))?;

            self.conditional_enforce_equal(cs.ns(|| "conditional_enforce_equal"), other, &should_enforce_equal)?;
            self.conditional_enforce_not_equal(
                cs.ns(|| "conditional_enforce_not_equal"),
                other,
                &should_enforce_equal.not(),
            )?;

            Ok(should_enforce_equal)
        }
    }

    fn conditional_enforce_not_equal<CS: ConstraintSystem<BaseField>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => {
                if c1 == c2 {
                    should_enforce.enforce_equal(cs.ns(|| "enforce_equal"), &Boolean::Constant(false))?;
                }
                Ok(())
            }
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let c = AllocatedNonNativeFieldVar::alloc_constant(cs.ns(|| "alloc_constant"), || Ok(c))?;
                c.conditional_enforce_not_equal(&mut cs.ns(|| "conditional_enforce_not_equal"), v, should_enforce)
            }
            (Self::Var(v1), Self::Var(v2)) => {
                v1.conditional_enforce_not_equal(&mut cs.ns(|| "conditional_enforce_not_equal"), v2, should_enforce)
            }
        }
    }

    /// The `mul_without_reduce` for `NonNativeFieldVar`
    pub fn mul_without_reduce<CS: ConstraintSystem<BaseField>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<NonNativeFieldMulResultVar<TargetField, BaseField>, SynthesisError> {
        match self {
            Self::Constant(c) => match other {
                Self::Constant(other_c) => Ok(NonNativeFieldMulResultVar::Constant(*c * other_c)),
                Self::Var(other_v) => {
                    let self_v = AllocatedNonNativeFieldVar::<TargetField, BaseField>::alloc_constant(
                        cs.ns(|| "alloc_constant"),
                        || Ok(c),
                    )?;
                    Ok(NonNativeFieldMulResultVar::Variable(
                        other_v.mul_without_reduce(&mut cs.ns(|| "mul_without_reduce"), &self_v)?,
                    ))
                }
            },
            Self::Var(v) => {
                let other_v = match other {
                    Self::Constant(other_c) => AllocatedNonNativeFieldVar::<TargetField, BaseField>::alloc_constant(
                        &mut cs.ns(|| "alloc_constant"),
                        || Ok(other_c),
                    )?,
                    Self::Var(other_v) => other_v.clone(),
                };
                Ok(NonNativeFieldMulResultVar::Variable(
                    v.mul_without_reduce(&mut cs.ns(|| "mul_without_reduce"), &other_v)?,
                ))
            }
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> From<AllocatedNonNativeFieldVar<TargetField, BaseField>>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn from(other: AllocatedNonNativeFieldVar<TargetField, BaseField>) -> Self {
        Self::Var(other)
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> FieldGadget<TargetField, BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    type Variable = AllocatedNonNativeFieldVar<TargetField, BaseField>;

    fn get_value(&self) -> Option<TargetField> {
        match self {
            Self::Constant(v) => Some(*v),
            Self::Var(v) => Some(v.value().unwrap()),
        }
    }

    fn get_variable(&self) -> Self::Variable {
        match self {
            Self::Constant(_v) => unimplemented!(),
            Self::Var(v) => v.clone(),
        }
    }

    fn zero<CS: ConstraintSystem<BaseField>>(_: CS) -> Result<Self, SynthesisError> {
        Ok(Self::Constant(TargetField::zero()))
    }

    fn one<CS: ConstraintSystem<BaseField>>(_: CS) -> Result<Self, SynthesisError> {
        Ok(Self::Constant(TargetField::one()))
    }

    fn negate<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(-*c)),
            Self::Var(v) => Ok(Self::Var(v.negate(&mut cs)?)),
        }
    }

    fn conditionally_add_constant<CS: ConstraintSystem<BaseField>>(
        &self,
        mut _cs: CS,
        _bit: &Boolean,
        _coeff: TargetField,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn add<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => Ok(Self::Constant(*c1 + c2)),
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                Ok(Self::Var(v.add_constant(&mut cs.ns(|| "add_constant"), c)?))
            }
            (Self::Var(v1), Self::Var(v2)) => Ok(Self::Var(v1.add(&mut cs.ns(|| "add"), &v2)?)),
        }
    }

    fn add_constant<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: CS,
        other: &TargetField,
    ) -> Result<Self, SynthesisError> {
        self.add(cs, &Self::Constant(*other))
    }

    fn sub<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => Ok(Self::Constant(*c1 - c2)),
            (Self::Var(v), Self::Constant(c)) => Ok(Self::Var(v.sub_constant(&mut cs.ns(|| "sub_constant"), c)?)),
            (Self::Constant(c), Self::Var(v)) => {
                let temp = v.sub_constant(&mut cs.ns(|| "sub_constant"), c)?;
                Ok(Self::Var(temp.negate(&mut cs.ns(|| "negate"))?))
            }
            (Self::Var(v1), Self::Var(v2)) => Ok(Self::Var(v1.sub(&mut cs.ns(|| "sub"), &v2)?)),
        }
    }

    fn mul<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => Ok(Self::Constant(*c1 * c2)),
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                Ok(Self::Var(v.mul_constant(&mut cs.ns(|| "mul_constant"), c)?))
            }
            (Self::Var(v1), Self::Var(v2)) => Ok(Self::Var(v1.mul(&mut cs.ns(|| "mul"), &v2)?)),
        }
    }

    fn mul_by_constant<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: CS,
        other: &TargetField,
    ) -> Result<Self, SynthesisError> {
        self.mul(cs, &Self::Constant(*other))
    }

    fn inverse<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(c.inverse().unwrap_or_default())),
            Self::Var(v) => Ok(Self::Var(v.inverse(&mut cs)?)),
        }
    }

    fn frobenius_map<CS: ConstraintSystem<BaseField>>(&self, _: CS, power: usize) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant({
                let mut tmp = *c;
                tmp.frobenius_map(power);
                tmp
            })),
            Self::Var(v) => Ok(Self::Var(v.frobenius_map(power))),
        }
    }

    fn cost_of_mul() -> usize {
        unimplemented!()
    }

    fn cost_of_inv() -> usize {
        unimplemented!()
    }
}

/****************************************************************************/
/****************************************************************************/

impl<TargetField: PrimeField, BaseField: PrimeField> EqGadget<BaseField> for NonNativeFieldVar<TargetField, BaseField> {
    fn enforce_equal<CS: ConstraintSystem<BaseField>>(&self, cs: CS, other: &Self) -> Result<(), SynthesisError> {
        self.conditional_enforce_equal(cs, other, &Boolean::constant(true))
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> NEqGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn enforce_not_equal<CS: ConstraintSystem<BaseField>>(&self, cs: CS, other: &Self) -> Result<(), SynthesisError> {
        self.conditional_enforce_not_equal(cs, other, &Boolean::Constant(true))
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ConditionalEqGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn conditional_enforce_equal<CS: ConstraintSystem<BaseField>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => {
                if c1 != c2 {
                    condition.enforce_equal(cs.ns(|| "enforce_equal"), &Boolean::Constant(false))?;
                }
                Ok(())
            }
            (Self::Constant(c), Self::Var(v)) | (Self::Var(v), Self::Constant(c)) => {
                let c = AllocatedNonNativeFieldVar::alloc_constant(cs.ns(|| "alloc_constant"), || Ok(c))?;
                c.conditional_enforce_equal(&mut cs.ns(|| "conditional_enforce_equal"), v, condition)
            }
            (Self::Var(v1), Self::Var(v2)) => {
                v1.conditional_enforce_equal(&mut cs.ns(|| "conditional_enforce_equal"), v2, condition)
            }
        }
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBitsBEGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn to_bits_be<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        match self {
            Self::Constant(_) => self.to_bits_be_strict(cs.ns(|| "to_bits_strict")),
            Self::Var(v) => v.to_bits_be(cs.ns(|| "to_bits")),
        }
    }

    fn to_bits_be_strict<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(BitIteratorBE::new(&c.to_repr())
                .take((TargetField::Parameters::MODULUS_BITS) as usize)
                .map(Boolean::constant)
                .collect::<Vec<_>>()),
            Self::Var(v) => v.to_bits_be_strict(cs.ns(|| "to_bits_strict")),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBitsLEGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn to_bits_le<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        match self {
            Self::Constant(_) => self.to_bits_le_strict(cs.ns(|| "to_bits_strict")),
            Self::Var(v) => v.to_bits_le(cs.ns(|| "to_bits")),
        }
    }

    fn to_bits_le_strict<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(BitIteratorLE::new(&c.to_repr())
                .take((TargetField::Parameters::MODULUS_BITS) as usize)
                .map(Boolean::constant)
                .collect::<Vec<_>>()),
            Self::Var(v) => v.to_bits_le_strict(cs.ns(|| "to_bits_strict")),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBytesLEGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    /// Outputs the unique byte decomposition of `self` in *little-endian*
    /// form.
    fn to_bytes_le<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(&to_bytes_le![c].unwrap())),
            Self::Var(v) => v.to_bytes_le(cs.ns(|| "to_bytes")),
        }
    }

    fn to_bytes_le_strict<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(UInt8::constant_vec(&to_bytes_le![c].unwrap())),
            Self::Var(v) => v.to_bytes_le_strict(cs.ns(|| "to_bytes_strict")),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBytesBEGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    /// Outputs the unique byte decomposition of `self` in *little-endian*
    /// form.
    fn to_bytes_be<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        match self {
            Self::Constant(c) => {
                let bytes = &to_bytes_le![c].unwrap().into_iter().rev().collect::<Vec<u8>>();
                Ok(UInt8::constant_vec(bytes))
            }
            Self::Var(v) => v.to_bytes_be(cs.ns(|| "to_bytes")),
        }
    }

    fn to_bytes_be_strict<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        match self {
            Self::Constant(c) => {
                let bytes = &to_bytes_le![c].unwrap().into_iter().rev().collect::<Vec<u8>>();
                Ok(UInt8::constant_vec(bytes))
            }
            Self::Var(v) => v.to_bytes_be_strict(cs.ns(|| "to_bytes_strict")),
        }
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> CondSelectGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn conditionally_select<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        match cond {
            Boolean::Constant(true) => Ok(first.clone()),
            Boolean::Constant(false) => Ok(second.clone()),
            _ => {
                let first = match first {
                    Self::Constant(f) => {
                        AllocatedNonNativeFieldVar::alloc_constant(cs.ns(|| "alloc_constant_first"), || Ok(f))?
                    }
                    Self::Var(v) => v.clone(),
                };
                let second = match second {
                    Self::Constant(f) => {
                        AllocatedNonNativeFieldVar::alloc_constant(cs.ns(|| "alloc_constant_second"), || Ok(f))?
                    }
                    Self::Var(v) => v.clone(),
                };

                Ok(Self::Var(AllocatedNonNativeFieldVar::conditionally_select(
                    cs, &cond, &first, &second,
                )?))
            }
        }
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

/// Uses two bits to perform a lookup into a table
/// `b` is little-endian: `b[0]` is LSB.
impl<TargetField: PrimeField, BaseField: PrimeField> TwoBitLookupGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    type TableConstant = TargetField;

    fn two_bit_lookup<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        bits: &[Boolean],
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert_eq!(bits.len(), 2);
        debug_assert_eq!(constants.len(), 4);

        let mut constant = true;

        for b in bits {
            match b {
                Boolean::Is(_) | Boolean::Not(_) => constant = false,
                _ => {}
            }
        }

        if constant {
            // We're in the constant case

            let lsb = bits[0].get_value().get()? as usize;
            let msb = bits[1].get_value().get()? as usize;
            let index = lsb + (msb << 1);
            Ok(Self::Constant(constants[index]))
        } else {
            AllocatedNonNativeFieldVar::two_bit_lookup(cs.ns(|| "two_bit_lookup"), bits, constants).map(Self::Var)
        }
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ThreeBitCondNegLookupGadget<BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    type TableConstant = TargetField;

    fn three_bit_cond_neg_lookup<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        bits: &[Boolean],
        b0b1: &Boolean,
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert_eq!(bits.len(), 3);
        debug_assert_eq!(constants.len(), 4);

        let mut constant = matches!(b0b1, Boolean::Constant(_));

        for b in bits {
            match b {
                Boolean::Is(_) | Boolean::Not(_) => constant = false,
                _ => {}
            }
        }

        if constant {
            // We're in the constant case

            let lsb = bits[0].get_value().get()? as usize;
            let msb = bits[1].get_value().get()? as usize;
            let index = lsb + (msb << 1);
            let intermediate = constants[index];

            let is_negative = bits[2].get_value().get()?;
            let y = if is_negative { -intermediate } else { intermediate };
            Ok(Self::Constant(y))
        } else {
            AllocatedNonNativeFieldVar::three_bit_cond_neg_lookup(
                cs.ns(|| "three_bit_cond_neg_lookup"),
                bits,
                b0b1,
                constants,
            )
            .map(Self::Var)
        }
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> AllocGadget<TargetField, BaseField>
    for NonNativeFieldVar<TargetField, BaseField>
{
    fn alloc_constant<FN, T, CS: ConstraintSystem<BaseField>>(_cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TargetField>,
    {
        Ok(Self::Constant(*value_gen()?.borrow()))
    }

    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<BaseField>>(cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TargetField>,
    {
        AllocatedNonNativeFieldVar::alloc(cs, value_gen).map(Self::Var)
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<BaseField>>(cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TargetField>,
    {
        AllocatedNonNativeFieldVar::alloc_input(cs, value_gen).map(Self::Var)
    }
}

// TODO (raychu86): Find solution to pass through CS.
// impl<TargetField: PrimeField, BaseField: PrimeField> ToConstraintField<BaseField>
//     for NonNativeFieldVar<TargetField, BaseField>
// {
//     fn to_field_elements(&self) -> R1CSResult<Vec<BaseField>> {
//         // Use one group element to represent the optimization type.
//         //
//         // By default, the constant is converted in the weight-optimized type, because it results in fewer elements.
//         match self {
//             Self::Constant(c) => Ok(AllocatedNonNativeFieldVar::get_limbs_representations(
//                 c,
//                 OptimizationType::Weight,
//             )?
//             .into_iter()
//             .map(FpGadget::alloc_constant())
//             .collect()),
//             Self::Var(v) => v.to_constraint_field(),
//         }
//     }
// }
