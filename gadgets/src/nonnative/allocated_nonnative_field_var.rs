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
    bits::{Boolean, ToBitsBEGadget, ToBitsLEGadget, ToBytesGadget},
    fields::FpGadget,
    integers::uint::UInt8,
    nonnative::{
        allocated_nonnative_field_mul_result_var::AllocatedNonNativeFieldMulResultVar,
        reduce::{bigint_to_basefield, limbs_to_bigint, Reducer},
    },
    traits::{
        alloc::AllocGadget,
        eq::EqGadget,
        fields::FieldGadget,
        integers::integer::Integer,
        select::{CondSelectGadget, ThreeBitCondNegLookupGadget, TwoBitLookupGadget},
    },
};
use snarkvm_algorithms::{
    overhead,
    snark::marlin::params::{get_params, OptimizationType},
};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, Assignment, ConstraintSystem};
use snarkvm_utilities::{BigInteger, FromBits, ToBits};

use core::{
    borrow::Borrow,
    cmp::{max, min},
    marker::PhantomData,
};

/// The allocated version of `NonNativeFieldVar` (introduced below)
#[derive(Debug)]
pub struct AllocatedNonNativeFieldVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// The limbs, each of which is a BaseField gadget.
    pub limbs: Vec<FpGadget<BaseField>>,
    /// Number of additions done over this gadget, using which the gadget decides when to reduce.
    pub num_of_additions_over_normal_form: BaseField,
    /// Whether the limb representation is the normal form (using only the bits specified in the parameters, and the representation is strictly within the range of TargetField).
    pub is_in_the_normal_form: bool,
    #[doc(hidden)]
    pub target_phantom: PhantomData<TargetField>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> AllocatedNonNativeFieldVar<TargetField, BaseField> {
    /// Obtain the value of limbs
    pub fn limbs_to_value(limbs: Vec<BaseField>, optimization_type: OptimizationType) -> TargetField {
        let params = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), optimization_type);

        let mut base_repr: <TargetField as PrimeField>::BigInteger = TargetField::one().to_repr();

        // Convert 2^{(params.bits_per_limb - 1)} into the TargetField and then double the base
        // This is because 2^{(params.bits_per_limb)} might indeed be larger than the target field's prime.
        base_repr.muln((params.bits_per_limb - 1) as u32);
        let mut base: TargetField = TargetField::from_repr(base_repr).unwrap();
        base = base + base;

        let mut result = TargetField::zero();
        let mut power = TargetField::one();

        for limb in limbs.iter().rev() {
            let mut val = TargetField::zero();
            let mut cur = TargetField::one();

            // Iterate over limb bits (big endian).
            for bit in limb.to_repr().to_bits_be().iter().rev() {
                if *bit {
                    val += &cur;
                }
                cur.double_in_place();
            }

            result += &(val * power);
            power *= &base;
        }

        result
    }

    /// Obtain the value of a nonnative field element
    pub fn value(&self) -> Result<TargetField, SynthesisError> {
        let mut limbs = Vec::new();
        for limb in self.limbs.iter() {
            limbs.push(limb.get_value().get()?);
        }

        Ok(Self::limbs_to_value(limbs, self.get_optimization_type()))
    }

    /// Obtain the nonnative field element of a constant value
    pub fn constant<CS: ConstraintSystem<BaseField>>(cs: &mut CS, value: TargetField) -> Result<Self, SynthesisError> {
        // let optimization_type = match cs.optimization_goal() {
        //     OptimizationGoal::None => OptimizationType::Constraints,
        //     OptimizationGoal::Constraints => OptimizationType::Constraints,
        //     OptimizationGoal::Weight => OptimizationType::Weight,
        // };

        let optimization_type = OptimizationType::Weight;

        let limbs_value = Self::get_limbs_representations(&value, optimization_type)?;

        let mut limbs = Vec::new();

        for (i, limb_value) in limbs_value.iter().enumerate() {
            limbs.push(FpGadget::<BaseField>::alloc_constant(cs.ns(|| format!("alloc_constant_limb_{}", i)), || {
                Ok(limb_value)
            })?);
        }

        Ok(Self {
            limbs,
            num_of_additions_over_normal_form: BaseField::zero(),
            is_in_the_normal_form: true,
            target_phantom: PhantomData,
        })
    }

    /// Obtain the nonnative field element of one
    pub fn one<CS: ConstraintSystem<BaseField>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        Self::constant(cs, TargetField::one())
    }

    /// Obtain the nonnative field element of zero
    pub fn zero<CS: ConstraintSystem<BaseField>>(cs: &mut CS) -> Result<Self, SynthesisError> {
        Self::constant(cs, TargetField::zero())
    }

    /// Add a nonnative field element
    pub fn add<CS: ConstraintSystem<BaseField>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let mut limbs = Vec::new();
        for (i, (this_limb, other_limb)) in self.limbs.iter().zip(other.limbs.iter()).enumerate() {
            limbs.push(this_limb.add(cs.ns(|| format!("add_limb_{}", i)), other_limb)?);
        }

        let mut res = Self {
            limbs,
            num_of_additions_over_normal_form: self
                .num_of_additions_over_normal_form
                .add(&other.num_of_additions_over_normal_form)
                .add(&BaseField::one()),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        Reducer::<TargetField, BaseField>::post_add_reduce(cs, &mut res)?;
        Ok(res)
    }

    /// Add a constant
    pub fn add_constant<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: &mut CS,
        other: &TargetField,
    ) -> Result<Self, SynthesisError> {
        let other_limbs = Self::get_limbs_representations(other, self.get_optimization_type())?;

        let mut limbs = Vec::new();
        for (i, (this_limb, other_limb)) in self.limbs.iter().zip(other_limbs.iter()).enumerate() {
            limbs.push(this_limb.add_constant(cs.ns(|| format!("add_constant_{}", i)), other_limb)?);
        }

        let mut res = Self {
            limbs,
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form.add(&BaseField::one()),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        Reducer::<TargetField, BaseField>::post_add_reduce(cs, &mut res)?;

        Ok(res)
    }

    /// Subtract a nonnative field element, without the final reduction step
    pub fn sub_without_reduce<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let params = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), self.get_optimization_type());

        // Step 1: Reduce the `other` if needed
        let mut surfeit = overhead!(other.num_of_additions_over_normal_form + BaseField::one()) + 1;
        let mut other = other.clone();
        if (surfeit + params.bits_per_limb > BaseField::size_in_bits() - 1)
            || (surfeit + (TargetField::size_in_bits() - params.bits_per_limb * (params.num_limbs - 1))
                > BaseField::size_in_bits() - 1)
        {
            Reducer::reduce(cs, &mut other)?;
            surfeit = overhead!(other.num_of_additions_over_normal_form + BaseField::one()) + 1;
        }

        // Step 2: Construct the padding
        let mut pad_non_top_limb_repr: <BaseField as PrimeField>::BigInteger = BaseField::one().to_repr();
        let mut pad_top_limb_repr: <BaseField as PrimeField>::BigInteger = pad_non_top_limb_repr;

        pad_non_top_limb_repr.muln((surfeit + params.bits_per_limb) as u32);
        let pad_non_top_limb = BaseField::from_repr(pad_non_top_limb_repr).unwrap();

        pad_top_limb_repr
            .muln((surfeit + (TargetField::size_in_bits() - params.bits_per_limb * (params.num_limbs - 1))) as u32);
        let pad_top_limb = BaseField::from_repr(pad_top_limb_repr).unwrap();

        let mut pad_limbs = Vec::with_capacity(self.limbs.len());
        pad_limbs.push(pad_top_limb);
        for _ in 0..self.limbs.len() - 1 {
            pad_limbs.push(pad_non_top_limb);
        }

        // Step 3: Prepare to pad the padding to k * p for some k
        let pad_to_kp_gap = Self::limbs_to_value(pad_limbs, self.get_optimization_type()).neg();
        let pad_to_kp_limbs = Self::get_limbs_representations(&pad_to_kp_gap, self.get_optimization_type())?;

        // Step 4: The result is self + pad + pad_to_kp - other
        let mut limbs = Vec::new();
        for (i, ((this_limb, other_limb), pad_to_kp_limb)) in
            self.limbs.iter().zip(other.limbs.iter()).zip(pad_to_kp_limbs.iter()).enumerate()
        {
            if i != 0 {
                let temp = pad_non_top_limb + *pad_to_kp_limb;
                limbs.push(
                    this_limb
                        .add_constant(cs.ns(|| format!("add_constant_{}", i)), &temp)?
                        .sub(cs.ns(|| format!("sub_{}", i)), other_limb)?,
                );
            } else {
                let temp = pad_top_limb + *pad_to_kp_limb;
                limbs.push(
                    this_limb
                        .add_constant(cs.ns(|| format!("add_constant_{}", i)), &temp)?
                        .sub(cs.ns(|| format!("sub_{}", i)), other_limb)?,
                );
            }
        }

        let result = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            limbs,
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form
                + (other.num_of_additions_over_normal_form + BaseField::one())
                + (other.num_of_additions_over_normal_form + BaseField::one()),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        Ok(result)
    }

    /// Subtract a nonnative field element
    pub fn sub<CS: ConstraintSystem<BaseField>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let mut result = self.sub_without_reduce(&mut cs.ns(|| "sub_without_reduce"), other)?;
        Reducer::<TargetField, BaseField>::post_add_reduce(cs, &mut result)?;
        Ok(result)
    }

    /// Subtract a constant
    pub fn sub_constant<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: &mut CS,
        other: &TargetField,
    ) -> Result<Self, SynthesisError> {
        let constant = Self::constant(&mut cs.ns(|| "constant"), *other)?;

        self.sub(&mut cs.ns(|| "sub"), &constant)
    }

    /// Multiply a nonnative field element
    pub fn mul<CS: ConstraintSystem<BaseField>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        self.mul_without_reduce(cs, other)?.reduce(&mut cs.ns(|| "reduce"))
    }

    /// Multiply a constant
    pub fn mul_constant<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: &mut CS,
        other: &TargetField,
    ) -> Result<Self, SynthesisError> {
        let constant = Self::constant(&mut cs.ns(|| "constant"), *other)?;

        self.mul(&mut cs.ns(|| "mul"), &constant)
    }

    /// Compute the negate of a nonnative field element
    pub fn negate<CS: ConstraintSystem<BaseField>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let zero = Self::zero(&mut cs.ns(|| "zero"))?;
        zero.sub(&mut cs.ns(|| "sub"), self)
    }

    /// Compute the inverse of a nonnative field element
    pub fn inverse<CS: ConstraintSystem<BaseField>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let inverse =
            Self::alloc(&mut cs.ns(|| "alloc"), || Ok(self.value()?.inverse().unwrap_or_else(TargetField::zero)))?;

        let one = &Self::one(&mut cs.ns(|| "one"))?;

        let actual_result = self.mul(&mut cs.ns(|| "mul"), &inverse)?;
        actual_result.conditional_enforce_equal(
            &mut cs.ns(|| "conditional_enforce_equal"),
            one,
            &Boolean::Constant(true),
        )?;
        Ok(inverse)
    }

    /// Convert a `TargetField` element into limbs (not constraints)
    /// This is an internal function that would be reused by a number of other functions
    pub fn get_limbs_representations(
        elem: &TargetField,
        optimization_type: OptimizationType,
    ) -> Result<Vec<BaseField>, SynthesisError> {
        Self::get_limbs_representations_from_big_integer(&elem.to_repr(), optimization_type)
    }

    /// Obtain the limbs directly from a big int
    pub fn get_limbs_representations_from_big_integer(
        elem: &<TargetField as PrimeField>::BigInteger,
        optimization_type: OptimizationType,
    ) -> Result<Vec<BaseField>, SynthesisError> {
        let params = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), optimization_type);

        // Push the lower limbs first
        let mut limbs: Vec<BaseField> = Vec::new();
        let mut cur = *elem;
        for _ in 0..params.num_limbs {
            let cur_bits = cur.to_bits_be(); // `to_bits` is big endian
            let cur_mod_r =
                <BaseField as PrimeField>::BigInteger::from_bits_be(&cur_bits[cur_bits.len() - params.bits_per_limb..])
                    .unwrap(); // therefore, the lowest `bits_per_non_top_limb` bits is what we want.
            limbs.push(BaseField::from_repr(cur_mod_r).unwrap());
            cur.divn(params.bits_per_limb as u32);
        }

        // then we reserve, so that the limbs are ``big limb first''
        limbs.reverse();

        Ok(limbs)
    }

    /// For advanced use, multiply and output the intermediate representations (without reduction)
    /// This intermediate representations can be added with each other, and they can later be reduced back to the `NonNativeFieldVar`.
    pub fn mul_without_reduce<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<AllocatedNonNativeFieldMulResultVar<TargetField, BaseField>, SynthesisError> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let params = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), self.get_optimization_type());

        // Step 1: Reduce `self` and `other` if necessary
        let mut self_reduced = self.clone();
        let mut other_reduced = other.clone();
        Reducer::<TargetField, BaseField>::pre_mul_reduce(
            &mut cs.ns(|| "pre_mul_reduce"),
            &mut self_reduced,
            &mut other_reduced,
        )?;

        let mut prod_limbs = Vec::new();

        // We currently only support constraint optimization

        for z_index in 0..2 * params.num_limbs - 1 {
            prod_limbs.push(FpGadget::alloc(cs.ns(|| format!("limb product_{}", z_index)), || {
                let mut z_i = BaseField::zero();
                for i in 0..=min(params.num_limbs - 1, z_index) {
                    let j = z_index - i;
                    if j < params.num_limbs {
                        z_i += &self_reduced.limbs[i]
                            .get_value()
                            .unwrap()
                            .mul(&other_reduced.limbs[j].get_value().unwrap());
                    }
                }

                Ok(z_i)
            })?);
        }

        for c in 0..(2 * params.num_limbs - 1) {
            let c_pows: Vec<_> = (0..(2 * params.num_limbs - 1))
                .map(|i| BaseField::from((c + 1) as u128).pow(&vec![i as u64]))
                .collect();

            let mut x = FpGadget::zero(&mut cs.ns(|| format!("zero_x_{}", c)))?;
            let mut y = FpGadget::zero(&mut cs.ns(|| format!("zero_y_{}", c)))?;
            let mut z = FpGadget::zero(&mut cs.ns(|| format!("zero_z_{}", c)))?;

            for (i, (var, c_pow)) in self_reduced.limbs.iter().zip(c_pows.iter()).enumerate() {
                let temp =
                    var.mul_by_constant(&mut cs.ns(|| format!("var_mul_by_constant_c_pow_x_{}_{}", c, i)), c_pow)?;

                x = x.add(&mut cs.ns(|| format!("sum_add_x_{}_{}", c, i)), &temp)?
            }

            for (i, (var, c_pow)) in other_reduced.limbs.iter().zip(c_pows.iter()).enumerate() {
                let temp =
                    var.mul_by_constant(&mut cs.ns(|| format!("var_mul_by_constant_c_pow_y_{}_{}", c, i)), c_pow)?;

                y = y.add(&mut cs.ns(|| format!("sum_add_y_{}_ {}", c, i)), &temp)?
            }

            for (i, (var, c_pow)) in prod_limbs.iter().zip(c_pows.iter()).enumerate() {
                let temp =
                    var.mul_by_constant(&mut cs.ns(|| format!("var_mul_by_constant_c_pow_z_{}_{}", c, i)), c_pow)?;

                z = z.add(&mut cs.ns(|| format!("sum_add_z_{}_{}", c, i)), &temp)?
            }

            let x_mul_y = x.mul(cs.ns(|| format!("x_mul_y_{}", c)), &y)?;

            z.enforce_equal(cs.ns(|| format!("enforce_equal_{}", c)), &x_mul_y)?;
        }

        Ok(AllocatedNonNativeFieldMulResultVar {
            limbs: prod_limbs,
            prod_of_num_of_additions: (self_reduced.num_of_additions_over_normal_form + BaseField::one())
                * (other_reduced.num_of_additions_over_normal_form + BaseField::one()),
            target_phantom: PhantomData,
        })
    }

    pub(crate) fn frobenius_map(&self, _power: usize) -> Self {
        self.clone()
    }

    pub(crate) fn conditional_enforce_equal<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: &mut CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let field_parameters =
            get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), self.get_optimization_type());

        // Step 1: Get modulus p
        let p_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations_from_big_integer(
                &<TargetField as PrimeField>::Parameters::MODULUS,
                self.get_optimization_type(),
            )?;
        let p_bigint = limbs_to_bigint(field_parameters.bits_per_limb, &p_representations);

        let mut p_gadget_limbs = Vec::new();
        for limb in p_representations.iter() {
            p_gadget_limbs.push(FpGadget::<BaseField>::Constant(*limb));
        }
        let p_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: BaseField::one(),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        // Step 2: Get delta = self - other
        let zero = Self::zero(&mut cs.ns(|| "zero"))?;
        let mut delta = self.sub_without_reduce(&mut cs.ns(|| "sub_without_reduce"), other)?;
        delta = Self::conditionally_select(&mut cs.ns(|| "cond_select"), should_enforce, &delta, &zero)?;

        // Step 3: Allocate k = delta / p
        let k_gadget = FpGadget::<BaseField>::alloc(cs.ns(|| "k"), || {
            let mut delta_limbs_values = Vec::<BaseField>::new();
            for limb in delta.limbs.iter() {
                delta_limbs_values.push(limb.get_value().get()?);
            }

            let delta_bigint = limbs_to_bigint(field_parameters.bits_per_limb, &delta_limbs_values);

            Ok(bigint_to_basefield::<BaseField>(&(delta_bigint / p_bigint)))
        })?;

        let surfeit = overhead!(delta.num_of_additions_over_normal_form + BaseField::one()) + 1;
        Reducer::<TargetField, BaseField>::limb_to_bits_be(&mut cs.ns(|| "limb_to_bits"), &k_gadget, surfeit)?;

        // Step 4: Compute k * p
        let mut kp_gadget_limbs = Vec::new();
        for (i, limb) in p_gadget.limbs.iter().enumerate() {
            kp_gadget_limbs.push(limb.mul(cs.ns(|| format!("mul_limb_{}", i)), &k_gadget)?);
        }

        // Step 5: Enforce delta = kp
        Reducer::<TargetField, BaseField>::group_and_check_equality(
            cs,
            surfeit,
            field_parameters.bits_per_limb,
            field_parameters.bits_per_limb,
            &delta.limbs,
            &kp_gadget_limbs,
        )?;

        Ok(())
    }

    pub(crate) fn conditional_enforce_not_equal<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: &mut CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let one = Self::one(&mut cs.ns(|| "one"))?;
        let subbed = &self.sub(&mut cs.ns(|| "sub"), other)?;

        let selected = Self::conditionally_select(cs.ns(|| "conditionally_select"), should_enforce, subbed, &one)?;
        selected.inverse(&mut cs.ns(|| "inverse"))?;

        Ok(())
    }

    pub(crate) fn get_optimization_type(&self) -> OptimizationType {
        // TODO (raychu86): Implement optimization goal.

        // match self.cs().optimization_goal() {
        //     OptimizationGoal::None => OptimizationType::Constraints,
        //     OptimizationGoal::Constraints => OptimizationType::Constraints,
        //     OptimizationGoal::Weight => OptimizationType::Weight,
        // }

        OptimizationType::Weight
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBitsBEGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    fn to_bits_be<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let field_parameters =
            get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), self.get_optimization_type());

        // Reduce to the normal form
        // Though, a malicious prover can make it slightly larger than p
        let mut self_normal = self.clone();
        Reducer::<TargetField, BaseField>::pre_eq_reduce(&mut cs.ns(|| "pre_eq_reduce"), &mut self_normal)?;

        // Therefore, we convert it to bits and enforce that it is in the field
        let mut bits = Vec::<Boolean>::new();
        for (i, limb) in self_normal.limbs.iter().enumerate() {
            bits.extend_from_slice(&Reducer::<TargetField, BaseField>::limb_to_bits_be(
                &mut cs.ns(|| format!("limb_to_bits_{}", i)),
                limb,
                field_parameters.bits_per_limb,
            )?);
        }
        bits.truncate(TargetField::size_in_bits());

        let mut b = TargetField::characteristic().to_vec();
        assert_eq!(b[0] % 2, 1);
        b[0] -= 1; // This works, because the LSB is one, so there's no borrows.
        let run = Boolean::enforce_smaller_or_equal_than_be(cs.ns(|| "enforce_smaller_or_equal_than_be"), &bits, b)?;

        // We should always end in a "run" of zeros, because
        // the characteristic is an odd prime. So, this should
        // be empty.
        assert!(run.is_empty());

        Ok(bits)
    }

    fn to_bits_be_strict<CS: ConstraintSystem<BaseField>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        self.to_bits_be(cs)
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBitsLEGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    fn to_bits_le<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let field_parameters =
            get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), self.get_optimization_type());

        // Reduce to the normal form
        // Though, a malicious prover can make it slightly larger than p
        let mut self_normal = self.clone();
        Reducer::<TargetField, BaseField>::pre_eq_reduce(&mut cs.ns(|| "pre_eq_reduce"), &mut self_normal)?;

        // Therefore, we convert it to bits and enforce that it is in the field
        let mut bits = Vec::<Boolean>::new();
        for (i, limb) in self_normal.limbs.iter().enumerate() {
            bits.extend_from_slice(&Reducer::<TargetField, BaseField>::limb_to_bits_be(
                &mut cs.ns(|| format!("limb_to_bits_{}", i)),
                limb,
                field_parameters.bits_per_limb,
            )?);
        }
        bits.reverse();
        bits.truncate(TargetField::size_in_bits());

        let mut b = TargetField::characteristic().to_vec();
        assert_eq!(b[0] % 2, 1);
        b[0] -= 1; // This works, because the LSB is one, so there's no borrows.
        let run = Boolean::enforce_smaller_or_equal_than_le(cs.ns(|| "enforce_smaller_or_equal_than_le"), &bits, b)?;

        // We should always end in a "run" of zeros, because
        // the characteristic is an odd prime. So, this should
        // be empty.
        assert!(run.is_empty());

        Ok(bits)
    }

    fn to_bits_le_strict<CS: ConstraintSystem<BaseField>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        self.to_bits_le(cs)
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ToBytesGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    fn to_bytes<CS: ConstraintSystem<BaseField>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let bits = self.to_bits_le(cs)?;

        let mut bytes = Vec::<UInt8>::new();
        bits.chunks(8).for_each(|bits_per_byte| {
            let mut bits_per_byte: Vec<Boolean> = bits_per_byte.to_vec();
            if bits_per_byte.len() < 8 {
                bits_per_byte.resize_with(8, || Boolean::constant(false));
            }

            bytes.push(UInt8::from_bits_le(&bits_per_byte));
        });

        Ok(bytes)
    }

    fn to_bytes_strict<CS: ConstraintSystem<BaseField>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> CondSelectGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    fn conditionally_select<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(first.get_optimization_type(), second.get_optimization_type());

        let mut limbs_sel = Vec::with_capacity(first.limbs.len());

        for (i, (x, y)) in first.limbs.iter().zip(&second.limbs).enumerate() {
            limbs_sel.push(FpGadget::<BaseField>::conditionally_select(
                cs.ns(|| format!("cond_select_{}", i)),
                cond,
                x,
                y,
            )?);
        }

        Ok(Self {
            limbs: limbs_sel,
            num_of_additions_over_normal_form: max(
                first.num_of_additions_over_normal_form,
                second.num_of_additions_over_normal_form,
            ),
            is_in_the_normal_form: first.is_in_the_normal_form && second.is_in_the_normal_form,
            target_phantom: PhantomData,
        })
    }

    fn cost() -> usize {
        1
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> TwoBitLookupGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    type TableConstant = TargetField;

    fn two_bit_lookup<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        bits: &[Boolean],
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(bits.len() == 2);
        debug_assert!(constants.len() == 4);

        let optimization_type = OptimizationType::Weight;

        let field_parameters = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), optimization_type);
        let mut limbs_constants = Vec::new();
        for _ in 0..field_parameters.num_limbs {
            limbs_constants.push(Vec::new());
        }

        for constant in constants.iter() {
            let representations = AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                constant,
                optimization_type,
            )?;

            for (i, representation) in representations.iter().enumerate() {
                limbs_constants[i].push(*representation);
            }
        }

        let mut limbs = Vec::new();
        for (i, limbs_constant) in limbs_constants.iter().enumerate() {
            limbs.push(FpGadget::<BaseField>::two_bit_lookup(
                &mut cs.ns(|| format!("two_bit_lookup_{}", i)),
                bits,
                limbs_constant,
            )?);
        }

        Ok(AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            limbs,
            num_of_additions_over_normal_form: BaseField::zero(),
            is_in_the_normal_form: true,
            target_phantom: PhantomData,
        })
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> ThreeBitCondNegLookupGadget<BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    type TableConstant = TargetField;

    fn three_bit_cond_neg_lookup<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        bits: &[Boolean],
        b0b1: &Boolean,
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(bits.len() == 3);
        debug_assert!(constants.len() == 4);

        let optimization_type = OptimizationType::Weight;

        let field_parameters = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), optimization_type);

        let mut limbs_constants = Vec::new();
        for _ in 0..field_parameters.num_limbs {
            limbs_constants.push(Vec::new());
        }

        for constant in constants.iter() {
            let representations = AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                constant,
                optimization_type,
            )?;

            for (i, representation) in representations.iter().enumerate() {
                limbs_constants[i].push(*representation);
            }
        }

        let mut limbs = Vec::new();
        for (i, limbs_constant) in limbs_constants.iter().enumerate() {
            limbs.push(FpGadget::<BaseField>::three_bit_cond_neg_lookup(
                cs.ns(|| format!("three_bit_cond_neg_lookup_{}", i)),
                bits,
                b0b1,
                limbs_constant,
            )?);
        }

        Ok(AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            limbs,
            num_of_additions_over_normal_form: BaseField::zero(),
            is_in_the_normal_form: true,
            target_phantom: PhantomData,
        })
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> AllocGadget<TargetField, BaseField>
    for AllocatedNonNativeFieldVar<TargetField, BaseField>
{
    #[inline]
    fn alloc_constant<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TargetField>,
    {
        let optimization_type = OptimizationType::Weight;

        let zero = TargetField::zero();

        let elem = match value_gen() {
            Ok(t) => *(t.borrow()),
            Err(_) => zero,
        };

        let elem_representations = Self::get_limbs_representations(&elem, optimization_type)?;
        let mut limbs = Vec::new();

        for (i, limb) in elem_representations.iter().enumerate() {
            limbs.push(FpGadget::<BaseField>::alloc_constant(cs.ns(|| format!("alloc_constant_limb_{}", i)), || {
                Ok(limb)
            })?);
        }

        let num_of_additions_over_normal_form = BaseField::zero();

        Ok(Self { limbs, num_of_additions_over_normal_form, is_in_the_normal_form: true, target_phantom: PhantomData })
    }

    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TargetField>,
    {
        let optimization_type = OptimizationType::Weight;

        let zero = TargetField::zero();

        let elem = match value_gen() {
            Ok(t) => *(t.borrow()),
            Err(_) => zero,
        };

        let elem_representations = Self::get_limbs_representations(&elem, optimization_type)?;
        let mut limbs = Vec::new();

        for (i, limb) in elem_representations.iter().enumerate() {
            limbs.push(FpGadget::<BaseField>::alloc(cs.ns(|| format!("alloc_{}", i)), || Ok(limb))?);
        }

        let num_of_additions_over_normal_form = BaseField::zero();

        Ok(Self { limbs, num_of_additions_over_normal_form, is_in_the_normal_form: true, target_phantom: PhantomData })
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<TargetField>,
    {
        let optimization_type = OptimizationType::Weight;

        let params = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), optimization_type);
        let zero = TargetField::zero();

        let elem = match value_gen() {
            Ok(t) => *(t.borrow()),
            Err(_) => zero,
        };

        let elem_representations = Self::get_limbs_representations(&elem, optimization_type)?;
        let mut limbs = Vec::new();

        for (i, limb) in elem_representations.iter().enumerate() {
            limbs.push(FpGadget::<BaseField>::alloc_input(cs.ns(|| format!("alloc_input_{}", i)), || Ok(limb))?);
        }

        let num_of_additions_over_normal_form = BaseField::one();

        // Only run for `inputs`

        for (i, limb) in limbs.iter().rev().take(params.num_limbs - 1).enumerate() {
            Reducer::<TargetField, BaseField>::limb_to_bits_be(
                &mut cs.ns(|| format!("limb_to_bits_{}", i)),
                limb,
                params.bits_per_limb,
            )?;
        }

        Reducer::<TargetField, BaseField>::limb_to_bits_be(
            &mut cs,
            &limbs[0],
            TargetField::size_in_bits() - (params.num_limbs - 1) * params.bits_per_limb,
        )?;

        Ok(Self { limbs, num_of_additions_over_normal_form, is_in_the_normal_form: false, target_phantom: PhantomData })
    }
}

// TODO (raychu86): Find solution to pass through CS.
// impl<TargetField: PrimeField, BaseField: PrimeField> ToConstraintField<BaseField>
//     for AllocatedNonNativeFieldVar<TargetField, BaseField>
// {
//     fn to_field_elements(&self) -> Result<Vec<BaseField>, SynthesisError> {
//         // provide a unique representation of the nonnative variable
//         // step 1: convert it into a bit sequence
//         let bits = self.to_bits()?;
//
//         // step 2: obtain the parameters for weight-optimized (often, fewer limbs)
//         let params = get_params(
//             TargetField::size_in_bits(),
//             BaseField::size_in_bits(),
//             OptimizationType::Weight,
//         );
//
//         // step 3: assemble the limbs
//         let mut limbs = bits
//             .chunks(params.bits_per_limb)
//             .map(|chunk| {
//                 let mut limb = FpGadget::<BaseField>::zero();
//                 let mut w = BaseField::one();
//                 for b in chunk.iter() {
//                     limb += FpGadget::from_boolean(b.clone()) * w;
//                     w.double_in_place();
//                 }
//                 limb
//             })
//             .collect::<Vec<BaseField>>();
//
//         limbs.reverse();
//
//         // step 4: output the limbs
//         Ok(limbs)
//     }
// }

/*
 * Implementation of a few traits
 */

impl<TargetField: PrimeField, BaseField: PrimeField> Clone for AllocatedNonNativeFieldVar<TargetField, BaseField> {
    fn clone(&self) -> Self {
        AllocatedNonNativeFieldVar {
            limbs: self.limbs.clone(),
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form,
            is_in_the_normal_form: self.is_in_the_normal_form,
            target_phantom: PhantomData,
        }
    }
}
