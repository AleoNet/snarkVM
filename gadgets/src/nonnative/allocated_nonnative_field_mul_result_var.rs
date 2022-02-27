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
    nonnative::{
        reduce::{bigint_to_basefield, limbs_to_bigint, Reducer},
        AllocatedNonNativeFieldVar,
    },
    traits::{alloc::AllocGadget, fields::FieldGadget},
};
use snarkvm_algorithms::{
    overhead,
    snark::marlin::params::{get_params, OptimizationType},
};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use core::marker::PhantomData;
use num_bigint::BigUint;

/// The allocated form of `NonNativeFieldMulResultVar` (introduced below)
#[derive(Debug)]
pub struct AllocatedNonNativeFieldMulResultVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// Limbs of the intermediate representations
    pub limbs: Vec<FpGadget<BaseField>>,
    /// The cumulative number of additions
    pub prod_of_num_of_additions: BaseField,
    #[doc(hidden)]
    pub target_phantom: PhantomData<TargetField>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> AllocatedNonNativeFieldMulResultVar<TargetField, BaseField> {
    /// Returns a `AllocatedNonNativeFieldMulResultVar` given a `AllocatedNonNativeFieldVar`.
    pub fn from_allocated_nonnative_field_gadget<CS: ConstraintSystem<BaseField>>(
        cs: &mut CS,
        src: &AllocatedNonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<Self, SynthesisError> {
        let field_parameters =
            get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), src.get_optimization_type());

        let mut limbs = src.limbs.clone();
        limbs.reverse();
        limbs.resize(2 * field_parameters.num_limbs - 1, FpGadget::<BaseField>::zero(cs)?);
        limbs.reverse();

        let prod_of_num_of_additions = src.num_of_additions_over_normal_form + BaseField::one();

        Ok(Self { limbs, prod_of_num_of_additions, target_phantom: PhantomData })
    }

    /// Get the value of the multiplication result
    pub fn value(&self) -> Result<TargetField, SynthesisError> {
        let params = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), self.get_optimization_type());

        let p_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations_from_big_integer(
                &<TargetField as PrimeField>::Parameters::MODULUS,
                self.get_optimization_type(),
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut limbs_values = Vec::<BaseField>::new();
        for limb in self.limbs.iter() {
            limbs_values.push(limb.get_value().unwrap_or_default());
        }
        let value_bigint = limbs_to_bigint(params.bits_per_limb, &limbs_values);

        let res = bigint_to_basefield::<TargetField>(&(value_bigint % p_bigint));
        Ok(res)
    }

    /// Constraints for reducing the result of a multiplication mod p, to get an original representation.
    pub fn reduce<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: &mut CS,
    ) -> Result<AllocatedNonNativeFieldVar<TargetField, BaseField>, SynthesisError> {
        let field_parameters =
            get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), self.get_optimization_type());

        // Step 1: Get the modulus p.
        let p_representations =
            AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations_from_big_integer(
                &<TargetField as PrimeField>::Parameters::MODULUS,
                self.get_optimization_type(),
            )?;
        let p_bigint = limbs_to_bigint(field_parameters.bits_per_limb, &p_representations);

        let mut p_gadget_limbs = Vec::new();
        for (i, limb) in p_representations.iter().enumerate() {
            p_gadget_limbs
                .push(FpGadget::<BaseField>::alloc_constant(cs.ns(|| format!("alloc_constant_{}", i)), || Ok(limb))?);
        }
        let p_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: BaseField::one(),
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        // Step 2: Compute surfeit
        let surfeit = overhead!(self.prod_of_num_of_additions + BaseField::one()) + 1 + 1;

        // Step 3: Allocate k
        let k_bits = {
            let mut result = Vec::new();

            let mut limbs_values = Vec::<BaseField>::new();
            for limb in self.limbs.iter() {
                limbs_values.push(limb.get_value().unwrap_or_default());
            }

            let value_bigint = limbs_to_bigint(field_parameters.bits_per_limb, &limbs_values);
            let mut k_cur = value_bigint / p_bigint;

            let total_length = TargetField::size_in_bits() + surfeit;

            for i in 0..total_length {
                result.push(Boolean::alloc(cs.ns(|| format!("alloc_{}", i)), || {
                    Ok(&k_cur % 2u64 == BigUint::from(1u64))
                })?);
                k_cur /= 2u64;
            }
            result
        };

        let k_limbs = {
            let zero = FpGadget::Constant(BaseField::zero());
            let mut limbs = Vec::new();

            let mut k_bits_cur = k_bits.clone();

            for i in 0..field_parameters.num_limbs {
                let this_limb_size = if i != field_parameters.num_limbs - 1 {
                    field_parameters.bits_per_limb
                } else {
                    k_bits.len() - (field_parameters.num_limbs - 1) * field_parameters.bits_per_limb
                };

                let this_limb_bits = k_bits_cur[0..this_limb_size].to_vec();
                k_bits_cur = k_bits_cur[this_limb_size..].to_vec();

                let mut limb = zero.clone();
                let mut cur = BaseField::one();

                for (j, bit) in this_limb_bits.iter().enumerate() {
                    // 1. limb += Fp(bit) * cur
                    let mut temp =
                        FpGadget::<BaseField>::from_boolean(cs.ns(|| format!("from_boolean_{}_{}", i, j)), *bit)?;
                    temp = temp.mul_by_constant(cs.ns(|| format!("mul_by_constant_{}_{}", i, j)), &cur)?;
                    limb = limb.add(cs.ns(|| format!("add_{}_{}", i, j)), &temp)?;

                    // 2. cur = 2 * cur
                    cur.double_in_place();
                }
                limbs.push(limb);
            }

            limbs.reverse();
            limbs
        };

        let k_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField> {
            limbs: k_limbs,
            num_of_additions_over_normal_form: self.prod_of_num_of_additions,
            is_in_the_normal_form: false,
            target_phantom: PhantomData,
        };

        let r_gadget = AllocatedNonNativeFieldVar::<TargetField, BaseField>::alloc(cs.ns(|| "r"), || self.value())?;

        let params = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), self.get_optimization_type());

        // Step 4: Reduce `self` and `other` if neceessary
        let mut prod_limbs = Vec::new();
        let zero = FpGadget::<BaseField>::zero(cs.ns(|| "zero"))?;

        for _ in 0..2 * params.num_limbs - 1 {
            prod_limbs.push(zero.clone());
        }

        for i in 0..params.num_limbs {
            for j in 0..params.num_limbs {
                let temp = p_gadget.limbs[i].mul(cs.ns(|| format!("mul_{}_{}", i, j)), &k_gadget.limbs[j])?;
                prod_limbs[i + j] = prod_limbs[i + j].add(cs.ns(|| format!("add_temp_{}_{}", i, j)), &temp)?;
            }
        }

        let mut kp_plus_r_gadget = Self {
            limbs: prod_limbs,
            prod_of_num_of_additions: (p_gadget.num_of_additions_over_normal_form + BaseField::one())
                * (k_gadget.num_of_additions_over_normal_form + BaseField::one()),
            target_phantom: PhantomData,
        };

        let kp_plus_r_limbs_len = kp_plus_r_gadget.limbs.len();
        for (i, limb) in r_gadget.limbs.iter().rev().enumerate() {
            kp_plus_r_gadget.limbs[kp_plus_r_limbs_len - 1 - i] =
                kp_plus_r_gadget.limbs[kp_plus_r_limbs_len - 1 - i].add(cs.ns(|| format!("add_limb{}", i)), limb)?;
        }

        Reducer::<TargetField, BaseField>::group_and_check_equality(
            &mut cs.ns(|| "group_and_check_equality"),
            surfeit,
            2 * params.bits_per_limb,
            params.bits_per_limb,
            &self.limbs,
            &kp_plus_r_gadget.limbs,
        )?;

        Ok(r_gadget)
    }

    /// Add unreduced elements.
    pub fn add<CS: ConstraintSystem<BaseField>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        assert_eq!(self.get_optimization_type(), other.get_optimization_type());

        let mut new_limbs = Vec::new();

        for (i, (l1, l2)) in self.limbs.iter().zip(other.limbs.iter()).enumerate() {
            let new_limb = l1.add(cs.ns(|| format!("add_{}", i)), l2)?;
            new_limbs.push(new_limb);
        }

        Ok(Self {
            limbs: new_limbs,
            prod_of_num_of_additions: self.prod_of_num_of_additions + other.prod_of_num_of_additions,
            target_phantom: PhantomData,
        })
    }

    /// Add native constant elem
    pub fn add_constant<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: &mut CS,
        other: &TargetField,
    ) -> Result<Self, SynthesisError> {
        let mut other_limbs = AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
            other,
            self.get_optimization_type(),
        )?;
        other_limbs.reverse();

        let mut new_limbs = Vec::new();

        for (i, limb) in self.limbs.iter().rev().enumerate() {
            if i < other_limbs.len() {
                new_limbs.push(limb.add_constant(cs.ns(|| format!("add_constant_{}", i)), &other_limbs[i])?);
            } else {
                new_limbs.push((*limb).clone());
            }
        }

        new_limbs.reverse();

        Ok(Self {
            limbs: new_limbs,
            prod_of_num_of_additions: self.prod_of_num_of_additions + BaseField::one(),
            target_phantom: PhantomData,
        })
    }

    pub(crate) fn get_optimization_type(&self) -> OptimizationType {
        // TODO (raychu86): Implement optimization goal for constraint system.

        // match self.cs().optimization_goal() {
        //     OptimizationGoal::None => OptimizationType::Constraints,
        //     OptimizationGoal::Constraints => OptimizationType::Constraints,
        //     OptimizationGoal::Weight => OptimizationType::Weight,
        // }

        OptimizationType::Weight
    }
}
