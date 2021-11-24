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

use snarkvm_algorithms::DefaultCapacityAlgebraicSponge;
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    bits::{Boolean, ToBitsBEGadget},
    fields::{AllocatedFp, FpGadget},
    integers::uint::UInt8,
    nonnative::{
        params::{get_params, OptimizationType},
        AllocatedNonNativeFieldVar,
        NonNativeFieldVar,
    },
    overhead,
    traits::{alloc::AllocGadget, fields::FieldGadget, integers::Integer},
    DefaultCapacityAlgebraicSpongeVar,
};
use snarkvm_r1cs::{ConstraintSystem, ConstraintVariable, LinearCombination, SynthesisError};

use crate::fiat_shamir::{traits::FiatShamirRngVar, FiatShamirAlgebraicSpongeRng};

use crate::{PhantomData, Vec};

/// Building the Fiat-Shamir sponge's gadget from any algebraic sponge's gadget.
#[derive(Clone)]
pub struct FiatShamirAlgebraicSpongeRngVar<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PS: DefaultCapacityAlgebraicSponge<BaseField, 6>,
    S: DefaultCapacityAlgebraicSpongeVar<BaseField, PS, 6>,
> {
    /// Algebraic sponge gadget.
    pub s: S,
    #[doc(hidden)]
    _target_field: PhantomData<TargetField>,
    #[doc(hidden)]
    _base_field: PhantomData<BaseField>,
    #[doc(hidden)]
    _sponge: PhantomData<PS>,
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PS: DefaultCapacityAlgebraicSponge<BaseField, 6>,
    S: DefaultCapacityAlgebraicSpongeVar<BaseField, PS, 6>,
> FiatShamirAlgebraicSpongeRngVar<TargetField, BaseField, PS, S>
{
    /// Compress every two elements if possible. Provides a vector of (limb, num_of_additions),
    /// both of which are BaseField.
    pub fn compress_gadgets<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        src_limbs: &[(FpGadget<BaseField>, BaseField)],
        ty: OptimizationType,
    ) -> Result<Vec<FpGadget<BaseField>>, SynthesisError> {
        let capacity = BaseField::size_in_bits() - 1;
        let mut dest_limbs = Vec::<FpGadget<BaseField>>::new();

        if src_limbs.is_empty() {
            return Ok(vec![]);
        }

        let params = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), ty);

        let adjustment_factor_lookup_table = {
            let mut table = Vec::<BaseField>::new();

            let mut cur = BaseField::one();
            for _ in 1..=capacity {
                table.push(cur);
                cur.double_in_place();
            }

            table
        };

        let mut i: usize = 0;
        let src_len = src_limbs.len();
        while i < src_len {
            let first = &src_limbs[i];
            let second = if i + 1 < src_len { Some(&src_limbs[i + 1]) } else { None };

            let first_max_bits_per_limb = params.bits_per_limb + overhead!(first.1 + BaseField::one());
            let second_max_bits_per_limb = if second.is_some() {
                params.bits_per_limb + overhead!(second.unwrap().1 + BaseField::one())
            } else {
                0
            };

            if second.is_some() && first_max_bits_per_limb + second_max_bits_per_limb <= capacity {
                let adjustment_factor = &adjustment_factor_lookup_table[second_max_bits_per_limb];

                let mut value = first.0.mul_by_constant(
                    cs.ns(|| format!("first_mul_by_constant_adjustment_factor_{}", i)),
                    adjustment_factor,
                )?;

                value = value.add(cs.ns(|| format!("value_add_second_{}", i)), &second.unwrap().0)?;

                dest_limbs.push(value);
                i += 2;
            } else {
                dest_limbs.push(first.0.clone());
                i += 1;
            }
        }

        Ok(dest_limbs)
    }

    /// Push gadgets to sponge.
    pub fn push_gadgets_to_sponge<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        sponge: &mut S,
        src: &[NonNativeFieldVar<TargetField, BaseField>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError> {
        let mut src_limbs: Vec<(FpGadget<BaseField>, BaseField)> = Vec::new();

        for (i, elem) in src.iter().enumerate() {
            match elem {
                NonNativeFieldVar::Constant(c) => {
                    let v = AllocatedNonNativeFieldVar::<TargetField, BaseField>::constant(
                        &mut cs.ns(|| format!("alloc_constant_{}", i)),
                        *c,
                    )?;

                    for limb in v.limbs {
                        let num_of_additions_over_normal_form =
                            if v.num_of_additions_over_normal_form == BaseField::zero() {
                                BaseField::one()
                            } else {
                                v.num_of_additions_over_normal_form
                            };
                        src_limbs.push((limb, num_of_additions_over_normal_form));
                    }
                }
                NonNativeFieldVar::Var(v) => {
                    for limb in v.limbs.clone() {
                        let num_of_additions_over_normal_form =
                            if v.num_of_additions_over_normal_form == BaseField::zero() {
                                BaseField::one()
                            } else {
                                v.num_of_additions_over_normal_form
                            };
                        src_limbs.push((limb, num_of_additions_over_normal_form));
                    }
                }
            }
        }

        let dest_limbs = Self::compress_gadgets(cs.ns(|| "compress_gadgets"), &src_limbs, ty)?;
        sponge.absorb(cs.ns(|| "absorb"), dest_limbs.iter())?;
        Ok(())
    }

    /// Obtain random bits from hashchain gadget. (Not guaranteed to be uniformly distributed,
    /// should only be used in certain situations.)
    pub fn get_booleans_from_sponge<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        sponge: &mut S,
        num_bits: usize,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let bits_per_element = BaseField::size_in_bits() - 1;
        let num_elements = (num_bits + bits_per_element - 1) / bits_per_element;

        let src_elements = sponge.squeeze_field_elements(cs.ns(|| "squeeze"), num_elements)?;
        let mut dest_bits = Vec::<Boolean>::new();

        for (i, elem) in src_elements.iter().enumerate() {
            let elem_bits = elem.to_bits_be(cs.ns(|| format!("elem_to_bits_{}", i)))?;
            dest_bits.extend_from_slice(&elem_bits[1..]); // discard the highest bit
        }

        Ok(dest_bits)
    }

    /// Obtain random elements from hashchain gadget. (Not guaranteed to be uniformly distributed,
    /// should only be used in certain situations.)
    pub fn get_gadgets_from_sponge<CS: ConstraintSystem<BaseField>>(
        cs: CS,
        sponge: &mut S,
        num_elements: usize,
        outputs_short_elements: bool,
    ) -> Result<Vec<NonNativeFieldVar<TargetField, BaseField>>, SynthesisError> {
        let (dest_gadgets, _) =
            Self::get_gadgets_and_bits_from_sponge(cs, sponge, num_elements, outputs_short_elements)?;

        Ok(dest_gadgets)
    }

    /// Obtain random elements, and the corresponding bits, from hashchain gadget. (Not guaranteed
    /// to be uniformly distributed, should only be used in certain situations.)
    #[allow(clippy::type_complexity)]
    pub fn get_gadgets_and_bits_from_sponge<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        sponge: &mut S,
        num_elements: usize,
        outputs_short_elements: bool,
    ) -> Result<(Vec<NonNativeFieldVar<TargetField, BaseField>>, Vec<Vec<Boolean>>), SynthesisError> {
        // TODO (raychu86): Assign optimization type properly.
        let optimization_type = OptimizationType::Weight;

        let params = get_params(
            TargetField::size_in_bits(),
            BaseField::size_in_bits(),
            optimization_type,
        );

        let num_bits_per_nonnative = if outputs_short_elements {
            128
        } else {
            TargetField::size_in_bits() - 1 // also omit the highest bit
        };
        let bits = Self::get_booleans_from_sponge(
            cs.ns(|| "get_booleans_from_sponge"),
            sponge,
            num_bits_per_nonnative * num_elements,
        )?;

        let mut lookup_table = Vec::<Vec<BaseField>>::new();
        let mut cur = TargetField::one();
        for _ in 0..num_bits_per_nonnative {
            let repr = AllocatedNonNativeFieldVar::<TargetField, BaseField>::get_limbs_representations(
                &cur,
                optimization_type,
            )?;
            lookup_table.push(repr);
            cur.double_in_place();
        }

        let mut dest_gadgets = Vec::<NonNativeFieldVar<TargetField, BaseField>>::new();
        let mut dest_bits = Vec::<Vec<Boolean>>::new();
        bits.chunks_exact(num_bits_per_nonnative)
            .enumerate()
            .for_each(|(i, per_nonnative_bits)| {
                let mut val = vec![BaseField::zero(); params.num_limbs];
                let mut lc = vec![LinearCombination::<BaseField>::zero(); params.num_limbs];

                let mut per_nonnative_bits_le = per_nonnative_bits.to_vec();
                per_nonnative_bits_le.reverse();

                dest_bits.push(per_nonnative_bits_le.clone());

                for (j, bit) in per_nonnative_bits_le.iter().enumerate() {
                    if bit.get_value().unwrap_or_default() {
                        for (k, val) in val.iter_mut().enumerate().take(params.num_limbs) {
                            *val += &lookup_table[j][k];
                        }
                    }

                    #[allow(clippy::needless_range_loop)]
                    for k in 0..params.num_limbs {
                        lc[k] = &lc[k] + bit.lc(CS::one(), BaseField::one()) * lookup_table[j][k];
                    }
                }

                let mut limbs = Vec::new();
                for k in 0..params.num_limbs {
                    let gadget = AllocatedFp::alloc(cs.ns(|| format!("alloc_{}_{}", i, k)), || Ok(val[k])).unwrap();

                    match &gadget.variable {
                        ConstraintVariable::Var(var) => {
                            lc[k] = lc[k].clone() - (BaseField::one(), *var);
                        }
                        ConstraintVariable::LC(linear_combination) => {
                            lc[k] = &lc[k] - (BaseField::one(), linear_combination);
                        }
                    }

                    cs.enforce(
                        || format!("enforce_constraint_{}_{}", i, k),
                        |lc| lc,
                        |lc| lc,
                        |_| lc[k].clone(),
                    );

                    limbs.push(FpGadget::<BaseField>::from(gadget));
                }

                dest_gadgets.push(NonNativeFieldVar::<TargetField, BaseField>::Var(
                    AllocatedNonNativeFieldVar::<TargetField, BaseField> {
                        limbs,
                        num_of_additions_over_normal_form: BaseField::zero(),
                        is_in_the_normal_form: true,
                        target_phantom: Default::default(),
                    },
                ));
            });

        Ok((dest_gadgets, dest_bits))
    }
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PS: DefaultCapacityAlgebraicSponge<BaseField, 6>,
    S: DefaultCapacityAlgebraicSpongeVar<BaseField, PS, 6>,
> FiatShamirRngVar<TargetField, BaseField, FiatShamirAlgebraicSpongeRng<TargetField, BaseField, PS>>
    for FiatShamirAlgebraicSpongeRngVar<TargetField, BaseField, PS, S>
{
    fn new<CS: ConstraintSystem<BaseField>>(cs: CS) -> Self {
        Self {
            s: S::with_parameters(cs, &PS::sample_parameters()),
            _target_field: PhantomData,
            _base_field: PhantomData,
            _sponge: PhantomData,
        }
    }

    fn constant<CS: ConstraintSystem<BaseField>>(
        cs: CS,
        pfs: &FiatShamirAlgebraicSpongeRng<TargetField, BaseField, PS>,
    ) -> Self {
        Self {
            s: S::constant(cs, &pfs.s.clone()),
            _target_field: PhantomData,
            _base_field: PhantomData,
            _sponge: PhantomData,
        }
    }

    fn absorb_nonnative_field_elements<CS: ConstraintSystem<BaseField>>(
        &mut self,
        cs: CS,
        elems: &[NonNativeFieldVar<TargetField, BaseField>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError> {
        Self::push_gadgets_to_sponge(cs, &mut self.s, &elems.to_vec(), ty)
    }

    fn absorb_native_field_elements<CS: ConstraintSystem<BaseField>>(
        &mut self,
        cs: CS,
        elems: &[FpGadget<BaseField>],
    ) -> Result<(), SynthesisError> {
        self.s.absorb(cs, elems.iter())?;
        Ok(())
    }

    fn absorb_bytes<CS: ConstraintSystem<BaseField>>(
        &mut self,
        mut cs: CS,
        elems: &[UInt8],
    ) -> Result<(), SynthesisError> {
        let capacity = BaseField::size_in_bits() - 1;
        let mut bits = Vec::<Boolean>::new();
        for elem in elems.iter() {
            let mut bits_le = elem.to_bits_le(); // UInt8's to_bits is le, which is an exception in Zexe.
            bits_le.reverse();
            bits.extend_from_slice(&bits_le);
        }

        let mut adjustment_factors = Vec::<BaseField>::new();
        let mut cur = BaseField::one();
        for _ in 0..capacity {
            adjustment_factors.push(cur);
            cur.double_in_place();
        }

        let mut gadgets = Vec::<FpGadget<BaseField>>::new();
        for (i, elem_bits) in bits.chunks(capacity).enumerate() {
            let mut elem = BaseField::zero();
            let mut lc = LinearCombination::zero();
            for (bit, adjustment_factor) in elem_bits.iter().rev().zip(adjustment_factors.iter()) {
                if bit.get_value().unwrap_or_default() {
                    elem += adjustment_factor;
                }
                lc = &lc + bit.lc(CS::one(), BaseField::one()) * *adjustment_factor;
            }

            let gadget = AllocatedFp::alloc(cs.ns(|| format!("alloc_{}", i)), || Ok(elem))?;

            match &gadget.variable {
                ConstraintVariable::Var(var) => {
                    lc = lc.clone() - (BaseField::one(), *var);
                }
                ConstraintVariable::LC(linear_combination) => {
                    lc = &lc - (BaseField::one(), linear_combination);
                }
            }

            gadgets.push(FpGadget::from(gadget));

            cs.enforce(|| format!("enforce_constraint_{}", i), |lc| lc, |lc| lc, |_| lc);
        }

        self.s.absorb(cs.ns(|| "absorb"), gadgets.iter())
    }

    fn squeeze_native_field_elements<CS: ConstraintSystem<BaseField>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<FpGadget<BaseField>>, SynthesisError> {
        self.s.squeeze_field_elements(cs, num)
    }

    fn squeeze_field_elements<CS: ConstraintSystem<BaseField>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<TargetField, BaseField>>, SynthesisError> {
        Self::get_gadgets_from_sponge(cs, &mut self.s, num, false)
    }

    #[allow(clippy::type_complexity)]
    fn squeeze_field_elements_and_bits<CS: ConstraintSystem<BaseField>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<(Vec<NonNativeFieldVar<TargetField, BaseField>>, Vec<Vec<Boolean>>), SynthesisError> {
        Self::get_gadgets_and_bits_from_sponge(cs, &mut self.s, num, false)
    }

    fn squeeze_128_bits_field_elements<CS: ConstraintSystem<BaseField>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<TargetField, BaseField>>, SynthesisError> {
        Self::get_gadgets_from_sponge(cs, &mut self.s, num, true)
    }

    #[allow(clippy::type_complexity)]
    fn squeeze_128_bits_field_elements_and_bits<CS: ConstraintSystem<BaseField>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<(Vec<NonNativeFieldVar<TargetField, BaseField>>, Vec<Vec<Boolean>>), SynthesisError> {
        Self::get_gadgets_and_bits_from_sponge(cs, &mut self.s, num, true)
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;
    use rand_chacha::ChaChaRng;
    use rand_core::SeedableRng;

    use snarkvm_curves::bls12_377::Fq;
    use snarkvm_fields::One;
    use snarkvm_gadgets::{bits::ToBitsLEGadget, traits::eq::EqGadget};
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::rand::UniformRand;

    use crate::fiat_shamir::{traits::FiatShamirRng, PoseidonSpongeGadget};
    use snarkvm_algorithms::crypto_hash::PoseidonSponge;

    use super::*;

    type PS = PoseidonSponge<Fq, 6, 1>;
    type PSGadget = PoseidonSpongeGadget<Fq, 6, 1>;
    type FS = FiatShamirAlgebraicSpongeRng<Fq, Fq, PS>;
    type FSGadget = FiatShamirAlgebraicSpongeRngVar<Fq, Fq, PS, PSGadget>;

    const MAX_ELEMENTS: usize = 50;
    const MAX_ELEMENT_SIZE: usize = 100;
    const ITERATIONS: usize = 50;

    const NUM_ABSORBED_RAND_FIELD_ELEMS: usize = 10;
    const NUM_ABSORBED_RAND_BYTE_ELEMS: usize = 10;
    const SIZE_ABSORBED_BYTE_ELEM: usize = 64;

    const NUM_SQUEEZED_FIELD_ELEMS: usize = 10;
    const NUM_SQUEEZED_SHORT_FIELD_ELEMS: usize = 10;

    // TODO (raychu86): Make a macro to test different optimization types.

    #[test]
    fn test_poseidon() {
        let rng = &mut ChaChaRng::seed_from_u64(123456789u64);

        let mut absorbed_rand_field_elems = Vec::new();
        for _ in 0..NUM_ABSORBED_RAND_FIELD_ELEMS {
            absorbed_rand_field_elems.push(Fq::rand(rng));
        }

        let mut absorbed_rand_byte_elems = Vec::<Vec<u8>>::new();
        for _ in 0..NUM_ABSORBED_RAND_BYTE_ELEMS {
            absorbed_rand_byte_elems.push((0..SIZE_ABSORBED_BYTE_ELEM).map(|_| u8::rand(rng)).collect());
        }

        // fs_rng in the plaintext world
        let mut fs_rng = FS::new();

        fs_rng.absorb_nonnative_field_elements(&absorbed_rand_field_elems, OptimizationType::Weight);

        for absorbed_rand_byte_elem in &absorbed_rand_byte_elems {
            fs_rng.absorb_bytes(absorbed_rand_byte_elem);
        }

        let squeezed_fields_elems = fs_rng
            .squeeze_nonnative_field_elements(NUM_SQUEEZED_FIELD_ELEMS, OptimizationType::Weight)
            .unwrap();
        let squeezed_short_fields_elems = fs_rng
            .squeeze_128_bits_nonnative_field_elements(NUM_SQUEEZED_SHORT_FIELD_ELEMS)
            .unwrap();

        // fs_rng in the constraint world
        let mut cs = TestConstraintSystem::<Fq>::new();
        let mut fs_rng_gadget = FSGadget::new(cs.ns(|| "new"));

        let mut absorbed_rand_field_elems_gadgets = Vec::new();
        for (i, absorbed_rand_field_elem) in absorbed_rand_field_elems.iter().enumerate() {
            absorbed_rand_field_elems_gadgets.push(
                NonNativeFieldVar::alloc(cs.ns(|| format!("alloc_constant_nonnative_field_var_{}", i)), || {
                    Ok(absorbed_rand_field_elem)
                })
                .unwrap(),
            );
        }
        fs_rng_gadget
            .absorb_nonnative_field_elements(
                cs.ns(|| "absorb_nonnative_fe"),
                &absorbed_rand_field_elems_gadgets,
                OptimizationType::Weight,
            )
            .unwrap();

        let mut absorbed_rand_byte_elems_gadgets = Vec::<Vec<UInt8>>::new();
        for absorbed_rand_byte_elem in absorbed_rand_byte_elems.iter() {
            let mut byte_gadget = Vec::<UInt8>::new();
            for byte in absorbed_rand_byte_elem.iter() {
                byte_gadget.push(UInt8::constant(*byte));
            }
            absorbed_rand_byte_elems_gadgets.push(byte_gadget);
        }
        for (i, absorbed_rand_byte_elems_gadget) in absorbed_rand_byte_elems_gadgets.iter().enumerate() {
            fs_rng_gadget
                .absorb_bytes(cs.ns(|| format!("absorb_bytes_{}", i)), absorbed_rand_byte_elems_gadget)
                .unwrap();
        }

        let squeezed_fields_elems_gadgets = fs_rng_gadget
            .squeeze_field_elements(cs.ns(|| "squeeze_fe"), NUM_SQUEEZED_FIELD_ELEMS)
            .unwrap();

        let squeezed_short_fields_elems_gadgets = fs_rng_gadget
            .squeeze_128_bits_field_elements(cs.ns(|| "squeeze_128_bits_fe"), NUM_SQUEEZED_SHORT_FIELD_ELEMS)
            .unwrap();

        // compare elems
        for (i, (left, right)) in squeezed_fields_elems
            .iter()
            .zip(squeezed_fields_elems_gadgets.iter())
            .enumerate()
        {
            assert_eq!(
                left.to_repr(),
                right.value().unwrap().to_repr(),
                "{}: left = {:?}, right = {:?}",
                i,
                left.to_repr(),
                right.value().unwrap().to_repr()
            );
        }

        // compare short elems
        for (i, (left, right)) in squeezed_short_fields_elems
            .iter()
            .zip(squeezed_short_fields_elems_gadgets.iter())
            .enumerate()
        {
            assert!(
                left.to_repr().eq(&right.value().unwrap().to_repr()),
                "{}: left = {:?}, right = {:?}",
                i,
                left.to_repr(),
                right.value().unwrap().to_repr()
            );
        }

        if !cs.is_satisfied() {
            println!("\n=========================================================");
            println!("\nUnsatisfied constraints:");
            println!("\n{:?}", cs.which_is_unsatisfied().unwrap());
            println!("\n=========================================================");
        }
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_compress_gadgets_weight_optimized() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        for i in 0..ITERATIONS {
            let mut cs = TestConstraintSystem::<Fq>::new();

            // Generate random elements.
            let num_elements: usize = rng.gen_range(0..MAX_ELEMENT_SIZE);
            let elements: Vec<_> = (0..num_elements).map(|_| Fq::rand(&mut rng)).collect();

            // Construct elements limb representations
            let mut element_limbs = Vec::<(Fq, Fq)>::new();
            let mut element_limb_gadgets = Vec::<(FpGadget<Fq>, Fq)>::new();

            for (j, elem) in elements.iter().enumerate() {
                let limbs =
                    AllocatedNonNativeFieldVar::<Fq, Fq>::get_limbs_representations(elem, OptimizationType::Weight)
                        .unwrap();
                for (k, limb) in limbs.iter().enumerate() {
                    let allocated_limb =
                        FpGadget::alloc(cs.ns(|| format!("alloc_limb_{}_{}_{}", i, j, k)), || Ok(limb)).unwrap();

                    element_limbs.push((*limb, Fq::one()));
                    element_limb_gadgets.push((allocated_limb, Fq::one()));
                    // Specifically set to one, since most gadgets in the constraint world would not have zero noise (due to the relatively weak normal form testing in `alloc`)
                }
            }

            // Compress the elements.
            let compressed_elements = FS::compress_elements(&element_limbs, OptimizationType::Weight);
            let compressed_element_gadgets = FSGadget::compress_gadgets(
                cs.ns(|| "compress_elements"),
                &element_limb_gadgets,
                OptimizationType::Weight,
            )
            .unwrap();

            // Check that the compressed results are equivalent.
            for (j, (gadget, element)) in compressed_element_gadgets.iter().zip(compressed_elements).enumerate() {
                // Allocate the field gadget from the base element.
                let alloc_element =
                    FpGadget::alloc(cs.ns(|| format!("alloc_field_{}_{}", i, j)), || Ok(element)).unwrap();

                // Check that the elements are equivalent.
                gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equal_element_{}_{}", i, j)), &alloc_element)
                    .unwrap();
            }
        }
    }

    #[test]
    fn test_compress_gadgets_constraint_optimized() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        for i in 0..ITERATIONS {
            let mut cs = TestConstraintSystem::<Fq>::new();

            // Generate random elements.
            let num_elements: usize = rng.gen_range(0..MAX_ELEMENT_SIZE);
            let elements: Vec<_> = (0..num_elements).map(|_| Fq::rand(&mut rng)).collect();

            // Construct elements limb representations
            let mut element_limbs = Vec::<(Fq, Fq)>::new();
            let mut element_limb_gadgets = Vec::<(FpGadget<Fq>, Fq)>::new();

            for (j, elem) in elements.iter().enumerate() {
                let limbs = AllocatedNonNativeFieldVar::<Fq, Fq>::get_limbs_representations(
                    elem,
                    OptimizationType::Constraints,
                )
                .unwrap();
                for (k, limb) in limbs.iter().enumerate() {
                    let allocated_limb =
                        FpGadget::alloc(cs.ns(|| format!("alloc_limb_{}_{}_{}", i, j, k)), || Ok(limb)).unwrap();

                    element_limbs.push((*limb, Fq::one()));
                    element_limb_gadgets.push((allocated_limb, Fq::one()));
                    // Specifically set to one, since most gadgets in the constraint world would not have zero noise (due to the relatively weak normal form testing in `alloc`)
                }
            }

            // Compress the elements.
            let compressed_elements = FS::compress_elements(&element_limbs, OptimizationType::Constraints);
            let compressed_element_gadgets = FSGadget::compress_gadgets(
                cs.ns(|| "compress_elements"),
                &element_limb_gadgets,
                OptimizationType::Constraints,
            )
            .unwrap();

            // Check that the compressed results are equivalent.
            for (j, (gadget, element)) in compressed_element_gadgets.iter().zip(compressed_elements).enumerate() {
                // Allocate the field gadget from the base element.
                let alloc_element =
                    FpGadget::alloc(cs.ns(|| format!("alloc_field_{}_{}", i, j)), || Ok(element)).unwrap();

                // Check that the elements are equivalent.
                gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equal_element_{}_{}", i, j)), &alloc_element)
                    .unwrap();
            }
        }
    }

    #[test]
    fn test_get_booleans_from_sponge() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        for i in 0..ITERATIONS {
            let mut cs = TestConstraintSystem::<Fq>::new();

            // Create a new FS rng and FS rng gadget.
            let mut fs_rng = FS::new();
            let mut fs_rng_gadget = FSGadget::new(cs.ns(|| format!("new_fs_rng_gadget_{}", i)));

            // Generate random element.
            let num_bytes: usize = rng.gen_range(0..MAX_ELEMENT_SIZE);
            let bytes: Vec<u8> = (0..num_bytes).map(|_| u8::rand(&mut rng)).collect();

            let mut byte_gadgets = vec![];
            for (j, byte) in bytes.iter().enumerate() {
                // Allocate the field gadget from the base element.
                let alloc_byte = UInt8::alloc(cs.ns(|| format!("alloc_byte_{}_{}", i, j)), || Ok(byte)).unwrap();

                byte_gadgets.push(alloc_byte);
            }

            // Absorb the bytes.
            fs_rng.absorb_bytes(&bytes);
            fs_rng_gadget
                .absorb_bytes(cs.ns(|| format!("absorb_bytes{}", i)), &byte_gadgets)
                .unwrap();

            // Get bits from the `fs_rng` and `fs_rng_gadget`.
            let num_bits = num_bytes * 8;
            let bits = FS::get_bits_from_sponge(&mut fs_rng.s, num_bits);
            let bit_gadgets = FSGadget::get_booleans_from_sponge(
                cs.ns(|| format!("get_booleans_from_sponge_{}", i)),
                &mut fs_rng_gadget.s,
                num_bits,
            )
            .unwrap();

            // Check that the bit results are equivalent.
            for (j, (bit_gadget, bit)) in bit_gadgets.iter().zip(bits).enumerate() {
                // Allocate a boolean from the native bit.
                let alloc_boolean =
                    Boolean::alloc(cs.ns(|| format!("alloc_boolean_result_{}_{}", i, j)), || Ok(bit)).unwrap();

                // Check that the boolean gadgets are equivalent.
                bit_gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equal_bit_{}_{}", i, j)), &alloc_boolean)
                    .unwrap();
            }
        }
    }

    #[test]
    fn test_squeeze_native_field_elements() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        for i in 0..ITERATIONS {
            let mut cs = TestConstraintSystem::<Fq>::new();

            // Create a new FS rng.
            let mut fs_rng = FS::new();

            // Allocate a new fs_rng gadget.
            let mut fs_rng_gadget = FSGadget::new(cs.ns(|| format!("fs_rng_gadget_new{}", i)));

            // Generate random elements.
            let num_elements: usize = rng.gen_range(0..MAX_ELEMENTS);
            let elements: Vec<_> = (0..num_elements).map(|_| Fq::rand(&mut rng)).collect();

            let mut element_gadgets = vec![];
            for (j, element) in elements.iter().enumerate() {
                // Allocate the nonnative field gadget from the base element.
                let alloc_element =
                    FpGadget::alloc(cs.ns(|| format!("native_alloc_field_{}_{}", i, j)), || Ok(element)).unwrap();

                element_gadgets.push(alloc_element);
            }

            // Push elements to the sponge
            fs_rng.absorb_native_field_elements(&elements);
            fs_rng_gadget
                .absorb_native_field_elements(cs.ns(|| format!("push_gadgets_to_sponge{}", i)), &element_gadgets)
                .unwrap();

            // Get the elements from the `fs_rng` and `fs_rng_gadget`.
            let squeeze_result = fs_rng.squeeze_native_field_elements(num_elements).unwrap();
            let gadget_squeeze_result = fs_rng_gadget
                .squeeze_native_field_elements(cs.ns(|| format!("squeeze_field_elements_{}", i)), num_elements)
                .unwrap();

            // Check that the squeeze results are equivalent.
            for (j, (gadget, element)) in gadget_squeeze_result.iter().zip(squeeze_result).enumerate() {
                // Allocate the nonnative field gadget from the base element.
                let alloc_element = FpGadget::alloc(cs.ns(|| format!("native_alloc_field_result{}_{}", i, j)), || {
                    Ok(element)
                })
                .unwrap();

                // Check that the elements are equivalent.
                gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equal_element_{}_{}", i, j)), &alloc_element)
                    .unwrap();
            }
        }
    }

    #[test]
    fn test_squeeze_nonnative_field_elements() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        for i in 0..ITERATIONS {
            let mut cs = TestConstraintSystem::<Fq>::new();

            // Create a new FS rng.
            let mut fs_rng = FS::new();

            // Allocate a new fs_rng gadget.
            let mut fs_rng_gadget = FSGadget::new(cs.ns(|| format!("fs_rng_gadget_new{}", i)));

            // Generate random elements.
            let num_elements: usize = rng.gen_range(0..MAX_ELEMENTS);
            let elements: Vec<_> = (0..num_elements).map(|_| Fq::rand(&mut rng)).collect();

            let mut element_gadgets = vec![];
            for (j, element) in elements.iter().enumerate() {
                // Allocate the nonnative field gadget from the base element.
                let alloc_element =
                    NonNativeFieldVar::alloc(cs.ns(|| format!("nonnative_alloc_field_{}_{}", i, j)), || Ok(element))
                        .unwrap();

                element_gadgets.push(alloc_element);
            }

            // Push elements to the sponge
            fs_rng.absorb_nonnative_field_elements(&elements, OptimizationType::Constraints);
            fs_rng_gadget
                .absorb_nonnative_field_elements(
                    cs.ns(|| format!("push_gadgets_to_sponge{}", i)),
                    &element_gadgets,
                    OptimizationType::Constraints,
                )
                .unwrap();

            // Get the elements from the `fs_rng` and `fs_rng_gadget`.
            let squeeze_result = fs_rng
                .squeeze_nonnative_field_elements(num_elements, OptimizationType::Constraints)
                .unwrap();
            let gadget_squeeze_result = fs_rng_gadget
                .squeeze_field_elements(cs.ns(|| format!("squeeze_field_elements_{}", i)), num_elements)
                .unwrap();

            // Check that the squeeze results are equivalent.
            for (j, (gadget, element)) in gadget_squeeze_result.iter().zip(squeeze_result).enumerate() {
                // Allocate the nonnative field gadget from the base element.
                let alloc_element =
                    NonNativeFieldVar::alloc(cs.ns(|| format!("nonnative_alloc_field_result{}_{}", i, j)), || {
                        Ok(element)
                    })
                    .unwrap();

                // Check that the elements are equivalent.
                gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equal_element_{}_{}", i, j)), &alloc_element)
                    .unwrap();
            }
        }
    }

    #[test]
    fn test_squeeze_field_elements_and_bits() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        for i in 0..ITERATIONS {
            let mut cs = TestConstraintSystem::<Fq>::new();

            // Create a new FS rng.
            let mut fs_rng = FS::new();

            // Allocate a new fs_rng gadget.
            let mut fs_rng_gadget = FSGadget::new(cs.ns(|| format!("fs_rng_gadget_new{}", i)));

            // Generate random elements.
            let num_elements: usize = rng.gen_range(0..MAX_ELEMENTS);
            let elements: Vec<_> = (0..num_elements).map(|_| Fq::rand(&mut rng)).collect();

            let mut element_gadgets = vec![];
            for (j, element) in elements.iter().enumerate() {
                // Allocate the nonnative field gadget from the base element.
                let alloc_element =
                    NonNativeFieldVar::alloc(cs.ns(|| format!("nonnative_alloc_field_{}_{}", i, j)), || Ok(element))
                        .unwrap();

                element_gadgets.push(alloc_element);
            }

            // Push elements to the sponge
            fs_rng.absorb_nonnative_field_elements(&elements, OptimizationType::Constraints);
            fs_rng_gadget
                .absorb_nonnative_field_elements(
                    cs.ns(|| format!("push_gadgets_to_sponge{}", i)),
                    &element_gadgets,
                    OptimizationType::Constraints,
                )
                .unwrap();

            // Get the elements from the `fs_rng` and `fs_rng_gadget`.
            let squeeze_result = fs_rng
                .squeeze_nonnative_field_elements(num_elements, OptimizationType::Constraints)
                .unwrap();
            let (gadget_squeeze_result, gadget_squeeze_bits) = fs_rng_gadget
                .squeeze_field_elements_and_bits(cs.ns(|| format!("squeeze_field_elements_{}", i)), num_elements)
                .unwrap();

            // Check that the squeeze results are equivalent.
            for (j, ((gadget, bits), element)) in gadget_squeeze_result
                .iter()
                .zip(gadget_squeeze_bits)
                .zip(squeeze_result)
                .enumerate()
            {
                // Allocate the nonnative field gadget from the base element.
                let alloc_element =
                    NonNativeFieldVar::alloc(cs.ns(|| format!("nonnative_alloc_field_result{}_{}", i, j)), || {
                        Ok(element)
                    })
                    .unwrap();

                // Check that the elements are equivalent.
                gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equal_element_{}_{}", i, j)), &alloc_element)
                    .unwrap();

                // Check that the bits are equivalent.
                let allocated_bits = alloc_element
                    .to_bits_le(cs.ns(|| format!("to_bits_le_{}_{}", i, j)))
                    .unwrap();

                for (k, (allocated_bit, bit)) in allocated_bits.iter().zip(bits).enumerate() {
                    allocated_bit
                        .enforce_equal(cs.ns(|| format!("enforce_equal_bit_{}_{}_{}", i, j, k)), &bit)
                        .unwrap();
                }
            }
        }
    }

    #[test]
    fn test_squeeze_128_bits_field_elements() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        for i in 0..ITERATIONS {
            let mut cs = TestConstraintSystem::<Fq>::new();

            // Create a new FS rng.
            let mut fs_rng = FS::new();

            // Allocate a new fs_rng gadget.
            let mut fs_rng_gadget = FSGadget::new(cs.ns(|| format!("fs_rng_gadget_new{}", i)));

            // Generate random elements.
            let num_elements: usize = rng.gen_range(0..MAX_ELEMENTS);
            let elements: Vec<_> = (0..num_elements).map(|_| Fq::rand(&mut rng)).collect();

            let mut element_gadgets = vec![];
            for (j, element) in elements.iter().enumerate() {
                // Allocate the nonnative field gadget from the base element.
                let alloc_element =
                    NonNativeFieldVar::alloc(cs.ns(|| format!("nonnative_alloc_field_{}_{}", i, j)), || Ok(element))
                        .unwrap();

                element_gadgets.push(alloc_element);
            }

            // Push elements to the sponge
            fs_rng.absorb_nonnative_field_elements(&elements, OptimizationType::Constraints);
            fs_rng_gadget
                .absorb_nonnative_field_elements(
                    cs.ns(|| format!("push_gadgets_to_sponge{}", i)),
                    &element_gadgets,
                    OptimizationType::Constraints,
                )
                .unwrap();

            // Get the elements from the `fs_rng` and `fs_rng_gadget`.
            let squeeze_result = fs_rng.squeeze_128_bits_nonnative_field_elements(num_elements).unwrap();
            let gadget_squeeze_result = fs_rng_gadget
                .squeeze_128_bits_field_elements(
                    cs.ns(|| format!("squeeze_128_bit_field_elements_{}", i)),
                    num_elements,
                )
                .unwrap();

            // Check that the squeeze results are equivalent.
            for (j, (gadget, element)) in gadget_squeeze_result.iter().zip(squeeze_result).enumerate() {
                // Allocate the nonnative field gadget from the base element.
                let alloc_element =
                    NonNativeFieldVar::alloc(cs.ns(|| format!("nonnative_alloc_field_result{}_{}", i, j)), || {
                        Ok(element)
                    })
                    .unwrap();

                // Check that the elements are equivalent.
                gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equal_element_{}_{}", i, j)), &alloc_element)
                    .unwrap();
            }
        }
    }

    #[test]
    fn test_squeeze_128_bits_field_elements_and_bits() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        for i in 0..ITERATIONS {
            let mut cs = TestConstraintSystem::<Fq>::new();

            // Create a new FS rng.
            let mut fs_rng = FS::new();

            // Allocate a new fs_rng gadget.
            let mut fs_rng_gadget = FSGadget::new(cs.ns(|| format!("fs_rng_gadget_new{}", i)));

            // Generate random elements.
            let num_elements: usize = rng.gen_range(0..MAX_ELEMENTS);
            let elements: Vec<_> = (0..num_elements).map(|_| Fq::rand(&mut rng)).collect();

            let mut element_gadgets = vec![];
            for (j, element) in elements.iter().enumerate() {
                // Allocate the nonnative field gadget from the base element.
                let alloc_element =
                    NonNativeFieldVar::alloc(cs.ns(|| format!("nonnative_alloc_field_{}_{}", i, j)), || Ok(element))
                        .unwrap();

                element_gadgets.push(alloc_element);
            }

            // Push elements to the sponge
            fs_rng.absorb_nonnative_field_elements(&elements, OptimizationType::Constraints);
            fs_rng_gadget
                .absorb_nonnative_field_elements(
                    cs.ns(|| format!("push_gadgets_to_sponge{}", i)),
                    &element_gadgets,
                    OptimizationType::Constraints,
                )
                .unwrap();

            // Get the elements from the `fs_rng` and `fs_rng_gadget`.
            let squeeze_result = fs_rng.squeeze_128_bits_nonnative_field_elements(num_elements).unwrap();
            let (gadget_squeeze_result, gadget_squeeze_bits) = fs_rng_gadget
                .squeeze_128_bits_field_elements_and_bits(
                    cs.ns(|| format!("squeeze_128_bit_field_elements_{}", i)),
                    num_elements,
                )
                .unwrap();

            // Check that the squeeze results are equivalent.
            for (j, ((gadget, bits), element)) in gadget_squeeze_result
                .iter()
                .zip(gadget_squeeze_bits)
                .zip(squeeze_result)
                .enumerate()
            {
                // Allocate the nonnative field gadget from the base element.
                let alloc_element =
                    NonNativeFieldVar::alloc(cs.ns(|| format!("nonnative_alloc_field_result{}_{}", i, j)), || {
                        Ok(element)
                    })
                    .unwrap();

                // Check that the elements are equivalent.
                gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equal_element_{}_{}", i, j)), &alloc_element)
                    .unwrap();

                // Check that the bits are equivalent.
                let allocated_bits = alloc_element
                    .to_bits_le(cs.ns(|| format!("to_bits_le_{}_{}", i, j)))
                    .unwrap();

                for (k, (allocated_bit, bit)) in allocated_bits.iter().zip(bits).enumerate() {
                    allocated_bit
                        .enforce_equal(cs.ns(|| format!("enforce_equal_bit_{}_{}_{}", i, j, k)), &bit)
                        .unwrap();
                }
            }
        }
    }
}
