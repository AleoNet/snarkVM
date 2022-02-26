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
    bits::Boolean,
    fields::FpGadget,
    nonnative::AllocatedNonNativeFieldVar,
    traits::{
        alloc::AllocGadget,
        eq::{ConditionalEqGadget, EqGadget},
        fields::FieldGadget,
    },
};
use snarkvm_algorithms::{overhead, snark::marlin::params::get_params};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::{BigInteger, BitIteratorBE, ToBits};

use core::{cmp::min, marker::PhantomData};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::identities::{One, Zero};

const fn num_bits<T>() -> usize {
    std::mem::size_of::<T>() * 8
}

fn log_2(x: usize) -> u32 {
    assert!(x > 0);
    num_bits::<usize>() as u32 - x.leading_zeros() - 1
}

pub fn limbs_to_bigint<BaseField: PrimeField>(bits_per_limb: usize, limbs: &[BaseField]) -> BigUint {
    let mut val = BigUint::zero();
    let mut big_cur = BigUint::one();
    let two = BigUint::from(2u32);
    for limb in limbs.iter().rev() {
        let limb_repr = limb.to_repr().to_bits_le();
        let mut small_cur = big_cur.clone();
        for limb_bit in limb_repr.iter() {
            if *limb_bit {
                val += &small_cur;
            }
            small_cur *= 2u32;
        }
        big_cur *= two.pow(bits_per_limb as u32);
    }

    val
}

pub fn bigint_to_basefield<BaseField: PrimeField>(bigint: &BigUint) -> BaseField {
    let mut val = BaseField::zero();
    let mut cur = BaseField::one();
    let bytes = bigint.to_bytes_be();

    let basefield_256 = BaseField::from_repr(<BaseField as PrimeField>::BigInteger::from(256)).unwrap();

    for byte in bytes.iter().rev() {
        let bytes_basefield = BaseField::from(*byte as u128);
        val += &(cur * bytes_basefield);

        cur *= &basefield_256;
    }

    val
}

/// the collections of methods for reducing the presentations
pub struct Reducer<TargetField: PrimeField, BaseField: PrimeField> {
    pub target_phantom: PhantomData<TargetField>,
    pub base_phantom: PhantomData<BaseField>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> Reducer<TargetField, BaseField> {
    /// convert limbs to bits (take at most `BaseField::size_in_bits() - 1` bits)
    /// This implementation would be more efficient than the original `to_bits`
    /// or `to_non_unique_bits` since we enforce that some bits are always zero.
    pub fn limb_to_bits_be<CS: ConstraintSystem<BaseField>>(
        cs: &mut CS,
        limb: &FpGadget<BaseField>,
        num_bits: usize,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let num_bits = min(BaseField::size_in_bits() - 1, num_bits);
        let mut bits_considered = Vec::with_capacity(num_bits);
        let limb_value = limb.get_value().unwrap_or_default();

        for b in BitIteratorBE::new(limb_value.to_repr()).skip(
            <<BaseField as PrimeField>::Parameters as FieldParameters>::REPR_SHAVE_BITS as usize
                + (BaseField::size_in_bits() - num_bits),
        ) {
            bits_considered.push(b);
        }

        match limb {
            FpGadget::Constant(_) => {
                let mut bits = vec![];
                for b in bits_considered {
                    bits.push(Boolean::Constant(b));
                }

                Ok(bits)
            }
            _ => {
                let mut bits = vec![];
                for (i, b) in bits_considered.iter().enumerate() {
                    bits.push(Boolean::alloc(cs.ns(|| format!("bit_{}", i)), || Ok(b))?);
                }

                let mut bit_sum = FpGadget::zero(cs.ns(|| "zero"))?;
                let mut coeff = BaseField::one();

                for (i, bit) in bits.iter().rev().enumerate() {
                    let temp = (FpGadget::<BaseField>::from_boolean(cs.ns(|| format!("from_boolean_{}", i)), *bit)?)
                        .mul_by_constant(cs.ns(|| format!("mul_by_coeff_{}", i)), &coeff)?;

                    bit_sum = bit_sum.add(cs.ns(|| format!("add_{}", i)), &temp)?;
                    coeff.double_in_place();
                }

                bit_sum.enforce_equal(cs.ns(|| "enforce_equal"), limb)?;

                Ok(bits)
            }
        }
    }

    /// Reduction to the normal form
    pub fn reduce<CS: ConstraintSystem<BaseField>>(
        cs: &mut CS,
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<(), SynthesisError> {
        let new_elem =
            AllocatedNonNativeFieldVar::alloc(cs.ns(|| "normal_form"), || Ok(elem.value().unwrap_or_default()))?;
        elem.conditional_enforce_equal(cs, &new_elem, &Boolean::Constant(true))?;
        *elem = new_elem;

        Ok(())
    }

    /// Reduction to be enforced after additions
    pub fn post_add_reduce<CS: ConstraintSystem<BaseField>>(
        cs: &mut CS,
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<(), SynthesisError> {
        let field_parameters =
            get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), elem.get_optimization_type());
        let surfeit = overhead!(elem.num_of_additions_over_normal_form + BaseField::one()) + 1;

        if BaseField::size_in_bits() > 2 * field_parameters.bits_per_limb + surfeit + 1 {
            Ok(())
        } else {
            Self::reduce(cs, elem)
        }
    }

    /// Reduction used before multiplication to reduce the representations in a way that allows efficient multiplication
    pub fn pre_mul_reduce<CS: ConstraintSystem<BaseField>>(
        cs: &mut CS,
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
        elem_other: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<(), SynthesisError> {
        assert_eq!(elem.get_optimization_type(), elem_other.get_optimization_type());

        let field_parameters =
            get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), elem.get_optimization_type());

        if 2 * field_parameters.bits_per_limb + log_2(field_parameters.num_limbs) as usize
            > BaseField::size_in_bits() - 1
        {
            panic!("The current limb parameters do not support multiplication.");
        }

        loop {
            let prod_of_num_of_additions = (elem.num_of_additions_over_normal_form + BaseField::one())
                * (elem_other.num_of_additions_over_normal_form + BaseField::one());
            let overhead_limb = overhead!(
                prod_of_num_of_additions.mul(
                    &BaseField::from_repr(<BaseField as PrimeField>::BigInteger::from(
                        (field_parameters.num_limbs) as u64
                    ))
                    .unwrap()
                )
            );
            let bits_per_mulresult_limb = 2 * (field_parameters.bits_per_limb + 1) + overhead_limb;

            if bits_per_mulresult_limb < BaseField::size_in_bits() {
                break;
            }

            if elem.num_of_additions_over_normal_form >= elem_other.num_of_additions_over_normal_form {
                Self::reduce(cs, elem)?;
            } else {
                Self::reduce(cs, elem_other)?;
            }
        }

        Ok(())
    }

    /// Reduction to the normal form
    pub fn pre_eq_reduce<CS: ConstraintSystem<BaseField>>(
        cs: &mut CS,
        elem: &mut AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<(), SynthesisError> {
        if elem.is_in_the_normal_form {
            return Ok(());
        }

        Self::reduce(cs, elem)
    }

    /// Group and check equality
    pub fn group_and_check_equality<CS: ConstraintSystem<BaseField>>(
        cs: &mut CS,
        surfeit: usize,
        bits_per_limb: usize,
        shift_per_limb: usize,
        left: &[FpGadget<BaseField>],
        right: &[FpGadget<BaseField>],
    ) -> Result<(), SynthesisError> {
        let zero = FpGadget::<BaseField>::zero(cs.ns(|| "group_and_check_equality_zero"))?;

        let mut limb_pairs = Vec::<(FpGadget<BaseField>, FpGadget<BaseField>)>::new();
        let num_limb_in_a_group =
            (BaseField::size_in_bits() - 1 - surfeit - 1 - 1 - 1 - (bits_per_limb - shift_per_limb)) / shift_per_limb;

        let shift_array = {
            let mut array = Vec::new();
            let mut cur = BaseField::one().to_repr();
            for _ in 0..num_limb_in_a_group {
                array.push(BaseField::from_repr(cur).unwrap());
                cur.muln(shift_per_limb as u32);
            }

            array
        };

        for (left_limb, right_limb) in left.iter().zip(right.iter()).rev() {
            // note: the `rev` operation is here, so that the first limb (and the first groupped limb) will be the least significant limb.
            limb_pairs.push((left_limb.clone(), right_limb.clone()));
        }

        let mut groupped_limb_pairs = Vec::<(FpGadget<BaseField>, FpGadget<BaseField>, usize)>::new();

        for (i, limb_pairs_in_a_group) in limb_pairs.chunks(num_limb_in_a_group).enumerate() {
            let mut left_total_limb = FpGadget::<BaseField>::zero(cs.ns(|| format!("left_zero_{}", i)))?;
            let mut right_total_limb = FpGadget::<BaseField>::zero(cs.ns(|| format!("right_zero_{}", i)))?;

            for (j, ((left_limb, right_limb), shift)) in
                limb_pairs_in_a_group.iter().zip(shift_array.iter()).enumerate()
            {
                let left =
                    left_limb.mul_by_constant(cs.ns(|| format!("left_limb_mul_by_constant_{}_{}", i, j)), shift)?;
                left_total_limb = left_total_limb.add(cs.ns(|| format!("add_left_limb_{}_{}", i, j)), &left)?;

                let right =
                    right_limb.mul_by_constant(cs.ns(|| format!("right_limb_mul_by_constant_{}_{}", i, j)), shift)?;
                right_total_limb = right_total_limb.add(cs.ns(|| format!("add_right_limb_{}_{}", i, j)), &right)?;
            }

            groupped_limb_pairs.push((left_total_limb, right_total_limb, limb_pairs_in_a_group.len()));
        }

        // This part we mostly use the techniques in bellman-bignat
        // The following code is adapted from https://github.com/alex-ozdemir/bellman-bignat/blob/master/src/mp/bignat.rs#L567
        let mut carry_in = zero;
        let mut carry_in_value = BaseField::zero();
        let mut accumulated_extra = BigUint::zero();
        for (group_id, (left_total_limb, right_total_limb, num_limb_in_this_group)) in
            groupped_limb_pairs.iter().enumerate()
        {
            let mut pad_limb_repr: <BaseField as PrimeField>::BigInteger = BaseField::one().to_repr();

            pad_limb_repr.muln(
                (surfeit + (bits_per_limb - shift_per_limb) + shift_per_limb * num_limb_in_this_group + 1 + 1) as u32,
            );
            let pad_limb = BaseField::from_repr(pad_limb_repr).unwrap();

            let left_total_limb_value = left_total_limb.get_value().unwrap_or_default();
            let right_total_limb_value = right_total_limb.get_value().unwrap_or_default();

            let mut carry_value = left_total_limb_value + carry_in_value + pad_limb - right_total_limb_value;

            let mut carry_repr = carry_value.to_repr();
            carry_repr.divn((shift_per_limb * num_limb_in_this_group) as u32);

            carry_value = BaseField::from_repr(carry_repr).unwrap();

            let carry = FpGadget::<BaseField>::alloc(cs.ns(|| format!("alloc_{}", group_id)), || Ok(carry_value))?;

            accumulated_extra += limbs_to_bigint(bits_per_limb, &[pad_limb]);

            let (new_accumulated_extra, remainder) =
                accumulated_extra.div_rem(&BigUint::from(2u64).pow((shift_per_limb * num_limb_in_this_group) as u32));
            let remainder_limb = bigint_to_basefield::<BaseField>(&remainder);

            // Now check
            //      left_total_limb + pad_limb + carry_in - right_total_limb
            //   =  carry shift by (shift_per_limb * num_limb_in_this_group) + remainder

            let eqn_left = left_total_limb
                .add_constant(cs.ns(|| format!("add_constant_{}", group_id)), &pad_limb)?
                .add(cs.ns(|| format!("add_carry_in_{}", group_id)), &carry_in)?
                .sub(cs.ns(|| format!("sub_right_total_limb_{}", group_id)), right_total_limb)?;

            let eqn_right = &carry
                .mul_by_constant(
                    cs.ns(|| format!("mul_by_constant_{}", group_id)),
                    &BaseField::from(2u64).pow(&[(shift_per_limb * num_limb_in_this_group) as u64]),
                )?
                .add_constant(cs.ns(|| format!("add_by_constant_{}", group_id)), &remainder_limb)?;

            eqn_left.conditional_enforce_equal(
                cs.ns(|| format!("conditional_enforce_equal_{}", group_id)),
                eqn_right,
                &Boolean::Constant(true),
            )?;

            accumulated_extra = new_accumulated_extra;
            carry_in = carry.clone();
            carry_in_value = carry_value;

            if group_id == groupped_limb_pairs.len() - 1 {
                carry.enforce_equal(
                    cs.ns(|| format!("enforce_equal_{}", group_id)),
                    &FpGadget::<BaseField>::Constant(bigint_to_basefield(&accumulated_extra)),
                )?;
            } else {
                Reducer::<TargetField, BaseField>::limb_to_bits_be(
                    &mut cs.ns(|| format!("limb_to_bits_{}", group_id)),
                    &carry,
                    surfeit + bits_per_limb,
                )?;
            }
        }

        Ok(())
    }
}
