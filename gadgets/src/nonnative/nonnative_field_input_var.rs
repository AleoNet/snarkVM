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
    bits::boolean_input::BooleanInputGadget,
    fields::{AllocatedFp, FpGadget},
    nonnative::{AllocatedNonNativeFieldVar, NonNativeFieldVar},
    traits::{alloc::AllocGadget, eq::EqGadget, fields::FieldGadget},
    Boolean,
    FromFieldElementsGadget,
    MergeGadget,
    ToBitsLEGadget,
};
use snarkvm_algorithms::snark::marlin::params::{get_params, OptimizationType};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, LinearCombination, SynthesisError};

use core::{borrow::Borrow, marker::PhantomData, ops::Neg};

/// Conversion of field elements by allocating them as nonnative field elements
/// Used by Marlin
pub struct NonNativeFieldInputVar<F, CF>
where
    F: PrimeField,
    CF: PrimeField,
{
    /// Vector of nonnative field gadgets.
    pub val: Vec<NonNativeFieldVar<F, CF>>,
}

impl<F, CF> NonNativeFieldInputVar<F, CF>
where
    F: PrimeField,
    CF: PrimeField,
{
    /// Instantiate a new `NonNativeFieldInputVar`.
    pub fn new(val: Vec<NonNativeFieldVar<F, CF>>) -> Self {
        Self { val }
    }
}

impl<F, CF> IntoIterator for NonNativeFieldInputVar<F, CF>
where
    F: PrimeField,
    CF: PrimeField,
{
    type IntoIter = std::vec::IntoIter<NonNativeFieldVar<F, CF>>;
    type Item = NonNativeFieldVar<F, CF>;

    fn into_iter(self) -> Self::IntoIter {
        self.val.into_iter()
    }
}

impl<F, CF> Clone for NonNativeFieldInputVar<F, CF>
where
    F: PrimeField,
    CF: PrimeField,
{
    fn clone(&self) -> Self {
        Self { val: self.val.clone() }
    }
}

impl<F, CF> AllocGadget<Vec<F>, CF> for NonNativeFieldInputVar<F, CF>
where
    F: PrimeField,
    CF: PrimeField,
{
    fn alloc_constant<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<Vec<F>>, CS: ConstraintSystem<CF>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?;
        let mut allocated = Vec::<NonNativeFieldVar<F, CF>>::new();

        for (i, elem) in obj.borrow().iter().enumerate() {
            let elem_allocated =
                NonNativeFieldVar::<F, CF>::alloc_constant(cs.ns(|| format!("alloc_constant_element_{}", i)), || {
                    Ok(elem)
                })?;
            allocated.push(elem_allocated);
        }

        Ok(Self { val: allocated })
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<Vec<F>>, CS: ConstraintSystem<CF>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?;
        let mut allocated = Vec::<NonNativeFieldVar<F, CF>>::new();

        for (i, elem) in obj.borrow().iter().enumerate() {
            let elem_allocated =
                NonNativeFieldVar::<F, CF>::alloc(cs.ns(|| format!("alloc_element_{}", i)), || Ok(elem))?;
            allocated.push(elem_allocated);
        }

        Ok(Self { val: allocated })
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<Vec<F>>, CS: ConstraintSystem<CF>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        // TODO (raychu86): Select the optimization type properly.
        let optimization_type = OptimizationType::Weight;

        let params = get_params(F::size_in_bits(), CF::size_in_bits(), optimization_type);

        let obj = value_gen()?;

        // Step 1: use BooleanInputGadget to allocate the values as bits
        // This is to make sure that we are using as few elements as possible
        let boolean_allocation = BooleanInputGadget::alloc_input(cs.ns(|| "boolean"), || Ok(obj.borrow()))?;

        // Step 2: allocating the nonnative field elements as witnesses
        let mut field_allocation = Vec::<AllocatedNonNativeFieldVar<F, CF>>::new();

        for (i, elem) in obj.borrow().iter().enumerate() {
            let mut elem_allocated =
                AllocatedNonNativeFieldVar::<F, CF>::alloc(cs.ns(|| format!("allocating_element_{}", i)), || Ok(elem))?;

            // due to the consistency check below
            elem_allocated.is_in_the_normal_form = true;
            elem_allocated.num_of_additions_over_normal_form = CF::zero();

            field_allocation.push(elem_allocated);
        }

        // Step 3: check consistency
        for (i, (field_bits, field_elem)) in boolean_allocation.val.iter().zip(field_allocation.iter()).enumerate() {
            let mut field_bits = field_bits.clone();
            field_bits.reverse();

            let bit_per_top_limb = F::size_in_bits() - (params.num_limbs - 1) * params.bits_per_limb;
            let bit_per_non_top_limb = params.bits_per_limb;

            // must use lc to save computation
            for (j, limb) in field_elem.limbs.iter().enumerate() {
                let bits_slice = if j == 0 {
                    field_bits[0..bit_per_top_limb].to_vec()
                } else {
                    field_bits
                        [bit_per_top_limb + (j - 1) * bit_per_non_top_limb..bit_per_top_limb + j * bit_per_non_top_limb]
                        .to_vec()
                };

                let mut bit_sum = FpGadget::<CF>::zero(cs.ns(|| format!("zero_{}_{}", i, j)))?;
                let mut cur = CF::one();

                for (k, bit) in bits_slice.iter().rev().enumerate() {
                    let mut temp =
                        FpGadget::<CF>::from_boolean(cs.ns(|| format!("from_boolean_{}_{}_{}", i, j, k)), *bit)?;
                    temp = temp.mul_by_constant(cs.ns(|| format!("mul_by_constant_{}_{}_{}", i, j, k)), &cur)?;

                    bit_sum = bit_sum.add(cs.ns(|| format!("bit_sum_add_{}_{}_{}", i, j, k)), &temp)?;
                    cur.double_in_place();
                }

                limb.enforce_equal(cs.ns(|| format!("enforce_equal_{}_{}", i, j)), &bit_sum)?;
            }
        }

        let mut wrapped_field_allocation = Vec::<NonNativeFieldVar<F, CF>>::new();
        for field_gadget in field_allocation.iter() {
            wrapped_field_allocation.push(NonNativeFieldVar::Var(field_gadget.clone()));
        }
        Ok(Self { val: wrapped_field_allocation })
    }
}

impl<F: PrimeField, CF: PrimeField> FromFieldElementsGadget<F, CF> for NonNativeFieldInputVar<F, CF> {
    fn from_field_elements<CS: ConstraintSystem<CF>>(
        mut cs: CS,
        field_elements: &[FpGadget<CF>],
    ) -> Result<Self, SynthesisError> {
        // TODO (raychu86): Use constraint system specified optimization goal.

        // let optimization_type = match cs.optimization_goal() {
        //     OptimizationGoal::None => OptimizationType::Constraints,
        //     OptimizationGoal::Constraints => OptimizationType::Constraints,
        //     OptimizationGoal::Weight => OptimizationType::Weight,
        // };

        let optimization_type = OptimizationType::Weight;

        let params = get_params(F::size_in_bits(), CF::size_in_bits(), optimization_type);

        // Step 1: use BooleanInputGadget to convert them into booleans
        let boolean_allocation =
            BooleanInputGadget::<F, CF>::from_field_elements(cs.ns(|| "from_field_elements"), field_elements)?;

        // Step 2: construct the nonnative field gadgets from bits
        let mut field_allocation = Vec::<NonNativeFieldVar<F, CF>>::new();

        // reconstruct the field elements and check consistency
        for field_bits in boolean_allocation.val.iter() {
            let mut field_bits = field_bits.clone();
            field_bits.resize(F::size_in_bits(), Boolean::Constant(false));
            field_bits.reverse();

            let mut limbs = Vec::<FpGadget<CF>>::new();

            let bit_per_top_limb = F::size_in_bits() - (params.num_limbs - 1) * params.bits_per_limb;
            let bit_per_non_top_limb = params.bits_per_limb;

            // must use lc to save computation
            for j in 0..params.num_limbs {
                let bits_slice = if j == 0 {
                    field_bits[0..bit_per_top_limb].to_vec()
                } else {
                    field_bits
                        [bit_per_top_limb + (j - 1) * bit_per_non_top_limb..bit_per_top_limb + j * bit_per_non_top_limb]
                        .to_vec()
                };

                let mut lc = LinearCombination::<CF>::zero();
                let mut cur = CF::one();

                let mut limb_value = CF::zero();
                for bit in bits_slice.iter().rev() {
                    lc = &lc + bit.lc(CS::one(), CF::one()) * cur;
                    if bit.get_value().unwrap_or_default() {
                        limb_value += &cur;
                    }
                    cur.double_in_place();
                }

                let limb = AllocatedFp::<CF>::alloc(cs.ns(|| format!("limb_{}", j)), || Ok(limb_value))?;
                lc = &limb.variable.clone().neg() + lc;

                cs.enforce(|| format!("enforce_constraint_{}", j), |lc| lc, |lc| lc, |_| lc);

                limbs.push(FpGadget::from(limb));
            }

            field_allocation.push(NonNativeFieldVar::<F, CF>::Var(AllocatedNonNativeFieldVar::<F, CF> {
                limbs,
                num_of_additions_over_normal_form: CF::zero(),
                is_in_the_normal_form: true,
                target_phantom: PhantomData,
            }))
        }

        Ok(Self { val: field_allocation })
    }
}

impl<F: PrimeField, CF: PrimeField> MergeGadget<CF> for NonNativeFieldInputVar<F, CF> {
    fn merge<CS: ConstraintSystem<CF>>(&self, _cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        let mut elems = vec![];
        elems.extend_from_slice(&self.val);
        elems.extend_from_slice(&other.val);

        Ok(Self { val: elems })
    }

    fn merge_in_place<CS: ConstraintSystem<CF>>(&mut self, _cs: CS, other: &Self) -> Result<(), SynthesisError> {
        self.val.extend_from_slice(&other.val);

        Ok(())
    }
}

impl<F: PrimeField, CF: PrimeField> ToBitsLEGadget<CF> for NonNativeFieldInputVar<F, CF> {
    fn to_bits_le<CS: ConstraintSystem<CF>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let mut res = vec![];
        for (i, elem) in self.val.iter().enumerate() {
            res.extend_from_slice(&elem.to_bits_le(cs.ns(|| format!("to_bits_{}", i)))?);
        }
        Ok(res)
    }

    fn to_bits_le_strict<CS: ConstraintSystem<CF>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        self.to_bits_le(cs)
    }
}

#[cfg(test)]
mod test {

    use snarkvm_r1cs::{Fr, TestConstraintSystem};
    use snarkvm_utilities::rand::{test_rng, Uniform};

    use super::*;
    use crate::traits::eq::EqGadget;

    #[test]
    fn test_nonnative_field_inputs_from_field_elements() {
        let rng = &mut test_rng();

        let mut cs = TestConstraintSystem::<Fr>::new();

        let mut field_elements = vec![];
        let mut field_element_gadgets = vec![];

        // Construct the field elements and field element gadgets
        for i in 0..1 {
            let field_element = Fr::rand(rng);
            let field_element_gadget =
                FpGadget::alloc(cs.ns(|| format!("field element_{}", i)), || Ok(field_element)).unwrap();

            field_elements.push(field_element);
            field_element_gadgets.push(field_element_gadget);
        }

        // Construct expected field element bits

        let expected_nonnative_field_element_gadgets =
            NonNativeFieldInputVar::<Fr, Fr>::alloc(cs.ns(|| "alloc_nonnative_field_elements"), || Ok(field_elements))
                .unwrap();

        // Construct gadget nonnative field elements
        let nonnative_field_element_gadgets = NonNativeFieldInputVar::<Fr, Fr>::from_field_elements(
            cs.ns(|| "from_field_elements"),
            &field_element_gadgets,
        )
        .unwrap();

        for (i, (expected_nonnative_fe, nonnative_fe)) in expected_nonnative_field_element_gadgets
            .val
            .iter()
            .zip(nonnative_field_element_gadgets.val.iter())
            .enumerate()
        {
            expected_nonnative_fe
                .enforce_equal(cs.ns(|| format!("enforce_equal_nonnative_fe_{}", i)), nonnative_fe)
                .unwrap();
        }

        assert!(cs.is_satisfied());
    }
}
