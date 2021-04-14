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
    params::{get_params, OptimizationType},
    AllocatedNonNativeFieldVar,
    NonNativeFieldVar,
};

use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    fields::FpGadget,
    traits::fields::FieldGadget,
    utilities::{alloc::AllocGadget, boolean_input::BooleanInputGadget, eq::EqGadget},
};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use std::borrow::Borrow;

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
        let optimization_type = OptimizationType::Constraints;

        let params = get_params(F::size_in_bits(), CF::size_in_bits(), optimization_type);

        let obj = value_gen()?;

        // Step 1: use BooleanInputVar to allocate the values as bits
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
                    let mut temp = FpGadget::<CF>::from_boolean(
                        cs.ns(|| format!("from_boolean_{}_{}_{}", i, j, k)),
                        (*bit).clone(),
                    )?;
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
        Ok(Self {
            val: wrapped_field_allocation,
        })
    }
}
