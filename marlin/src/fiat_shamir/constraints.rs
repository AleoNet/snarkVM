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
    fiat_shamir::{AlgebraicSponge, FiatShamirAlgebraicSpongeRng, FiatShamirRng},
    overhead,
};

use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    fields::{AllocatedFp, FpGadget},
    traits::fields::FieldGadget,
    utilities::{
        alloc::AllocGadget,
        boolean::Boolean,
        uint::{UInt, UInt8},
        ToBitsBEGadget,
    },
};
use snarkvm_nonnative::{
    params::{get_params, OptimizationType},
    AllocatedNonNativeFieldVar,
    NonNativeFieldVar,
};
use snarkvm_r1cs::{ConstraintSystem, ConstraintVariable, LinearCombination, SynthesisError};
use std::marker::PhantomData;

/// Vars for a RNG for use in a Fiat-Shamir transform.
pub trait FiatShamirRngVar<F: PrimeField, CF: PrimeField, PFS: FiatShamirRng<F, CF>>: Clone {
    /// Create a new RNG.
    fn new<CS: ConstraintSystem<CF>>(cs: CS) -> Self;

    /// Instantiate from a plaintext fs_rng.
    fn constant<CS: ConstraintSystem<CF>>(cs: CS, pfs: &PFS) -> Self;

    /// Take in field elements.
    fn absorb_nonnative_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        elems: &[NonNativeFieldVar<F, CF>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError>;

    /// Take in field elements.
    fn absorb_native_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        elems: &[FpGadget<CF>],
    ) -> Result<(), SynthesisError>;

    /// Take in bytes.
    fn absorb_bytes<CS: ConstraintSystem<CF>>(&mut self, cs: CS, elems: &[UInt8]) -> Result<(), SynthesisError>;

    /// Output field elements.
    fn squeeze_native_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<FpGadget<CF>>, SynthesisError>;

    /// Output field elements.
    fn squeeze_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError>;

    /// Output field elements and the corresponding bits (this can reduce repeated computation).
    #[allow(clippy::type_complexity)]
    fn squeeze_field_elements_and_bits<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<(Vec<NonNativeFieldVar<F, CF>>, Vec<Vec<Boolean>>), SynthesisError>;

    /// Output field elements with only 128 bits.
    fn squeeze_128_bits_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError>;

    /// Output field elements with only 128 bits, and the corresponding bits (this can reduce
    /// repeated computation).
    #[allow(clippy::type_complexity)]
    fn squeeze_128_bits_field_elements_and_bits<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<(Vec<NonNativeFieldVar<F, CF>>, Vec<Vec<Boolean>>), SynthesisError>;
}

/// Trait for an algebraic sponge such as Poseidon.
pub trait AlgebraicSpongeVar<CF: PrimeField, PS: AlgebraicSponge<CF>>: Clone {
    /// Create the new sponge.
    fn new<CS: ConstraintSystem<CF>>(cs: CS) -> Self;

    /// Instantiate from a plaintext sponge.
    fn constant<CS: ConstraintSystem<CF>>(cs: CS, ps: &PS) -> Self;

    /// Take in field elements.
    fn absorb<CS: ConstraintSystem<CF>>(&mut self, cs: CS, elems: &[FpGadget<CF>]) -> Result<(), SynthesisError>;

    /// Output field elements.
    fn squeeze<CS: ConstraintSystem<CF>>(&mut self, cs: CS, num: usize) -> Result<Vec<FpGadget<CF>>, SynthesisError>;
}

/// Building the Fiat-Shamir sponge's gadget from any algebraic sponge's gadget.
#[derive(Clone)]
pub struct FiatShamirAlgebraicSpongeRngVar<
    F: PrimeField,
    CF: PrimeField,
    PS: AlgebraicSponge<CF>,
    S: AlgebraicSpongeVar<CF, PS>,
> {
    /// Algebraic sponge gadget.
    pub s: S,
    #[doc(hidden)]
    f_phantom: PhantomData<F>,
    cf_phantom: PhantomData<CF>,
    ps_phantom: PhantomData<PS>,
}

impl<F: PrimeField, CF: PrimeField, PS: AlgebraicSponge<CF>, S: AlgebraicSpongeVar<CF, PS>>
    FiatShamirAlgebraicSpongeRngVar<F, CF, PS, S>
{
    /// Compress every two elements if possible. Provides a vector of (limb, num_of_additions),
    /// both of which are CF.
    pub fn compress_gadgets<CS: ConstraintSystem<CF>>(
        mut cs: CS,
        src_limbs: &[(FpGadget<CF>, CF)],
        ty: OptimizationType,
    ) -> Result<Vec<FpGadget<CF>>, SynthesisError> {
        let capacity = CF::size_in_bits() - 1;
        let mut dest_limbs = Vec::<FpGadget<CF>>::new();

        if src_limbs.is_empty() {
            return Ok(vec![]);
        }

        let params = get_params(F::size_in_bits(), CF::size_in_bits(), ty);

        let adjustment_factor_lookup_table = {
            let mut table = Vec::<CF>::new();

            let mut cur = CF::one();
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

            let first_max_bits_per_limb = params.bits_per_limb + overhead!(first.1 + &CF::one());
            let second_max_bits_per_limb = if second.is_some() {
                params.bits_per_limb + overhead!(second.unwrap().1 + &CF::one())
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
    pub fn push_gadgets_to_sponge<CS: ConstraintSystem<CF>>(
        mut cs: CS,
        sponge: &mut S,
        src: &[NonNativeFieldVar<F, CF>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError> {
        let mut src_limbs: Vec<(FpGadget<CF>, CF)> = Vec::new();

        for (i, elem) in src.iter().enumerate() {
            match elem {
                NonNativeFieldVar::Constant(c) => {
                    let v = AllocatedNonNativeFieldVar::<F, CF>::alloc_constant(
                        cs.ns(|| format!("alloc_constant_{}", i)),
                        || Ok(c),
                    )?;

                    for limb in v.limbs.iter() {
                        let num_of_additions_over_normal_form = if v.num_of_additions_over_normal_form == CF::zero() {
                            CF::one()
                        } else {
                            v.num_of_additions_over_normal_form
                        };
                        src_limbs.push((limb.clone(), num_of_additions_over_normal_form));
                    }
                }
                NonNativeFieldVar::Var(v) => {
                    for limb in v.limbs.iter() {
                        let num_of_additions_over_normal_form = if v.num_of_additions_over_normal_form == CF::zero() {
                            CF::one()
                        } else {
                            v.num_of_additions_over_normal_form
                        };
                        src_limbs.push((limb.clone(), num_of_additions_over_normal_form));
                    }
                }
            }
        }

        let dest_limbs = Self::compress_gadgets(cs.ns(|| "compress_gadgets"), &src_limbs, ty)?;
        sponge.absorb(cs.ns(|| "absorb"), &dest_limbs)?;
        Ok(())
    }

    /// Obtain random bits from hashchain gadget. (Not guaranteed to be uniformly distributed,
    /// should only be used in certain situations.)
    pub fn get_booleans_from_sponge<CS: ConstraintSystem<CF>>(
        mut cs: CS,
        sponge: &mut S,
        num_bits: usize,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let bits_per_element = CF::size_in_bits() - 1;
        let num_elements = (num_bits + bits_per_element - 1) / bits_per_element;

        let src_elements = sponge.squeeze(cs.ns(|| "squeeze"), num_elements)?;
        let mut dest_bits = Vec::<Boolean>::new();

        for (i, elem) in src_elements.iter().enumerate() {
            let elem_bits = elem.to_bits_be(cs.ns(|| format!("elem_to_bits_{}", i)))?;
            dest_bits.extend_from_slice(&elem_bits[1..]); // discard the highest bit
        }

        Ok(dest_bits)
    }

    /// Obtain random elements from hashchain gadget. (Not guaranteed to be uniformly distributed,
    /// should only be used in certain situations.)
    pub fn get_gadgets_from_sponge<CS: ConstraintSystem<CF>>(
        cs: CS,
        sponge: &mut S,
        num_elements: usize,
        outputs_short_elements: bool,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError> {
        let (dest_gadgets, _) =
            Self::get_gadgets_and_bits_from_sponge(cs, sponge, num_elements, outputs_short_elements)?;

        Ok(dest_gadgets)
    }

    /// Obtain random elements, and the corresponding bits, from hashchain gadget. (Not guaranteed
    /// to be uniformly distributed, should only be used in certain situations.)
    #[allow(clippy::type_complexity)]
    pub fn get_gadgets_and_bits_from_sponge<CS: ConstraintSystem<CF>>(
        mut cs: CS,
        sponge: &mut S,
        num_elements: usize,
        outputs_short_elements: bool,
    ) -> Result<(Vec<NonNativeFieldVar<F, CF>>, Vec<Vec<Boolean>>), SynthesisError> {
        let optimization_type = OptimizationType::Constraints;

        let params = get_params(F::size_in_bits(), CF::size_in_bits(), optimization_type);

        let num_bits_per_nonnative = if outputs_short_elements {
            128
        } else {
            F::size_in_bits() - 1 // also omit the highest bit
        };
        let bits = Self::get_booleans_from_sponge(
            cs.ns(|| "get_booleans_from_sponge"),
            sponge,
            num_bits_per_nonnative * num_elements,
        )?;

        let mut lookup_table = Vec::<Vec<CF>>::new();
        let mut cur = F::one();
        for _ in 0..num_bits_per_nonnative {
            let repr = AllocatedNonNativeFieldVar::<F, CF>::get_limbs_representations(&cur, optimization_type)?;
            lookup_table.push(repr);
            cur.double_in_place();
        }

        let mut dest_gadgets = Vec::<NonNativeFieldVar<F, CF>>::new();
        let mut dest_bits = Vec::<Vec<Boolean>>::new();
        bits.chunks_exact(num_bits_per_nonnative)
            .enumerate()
            .for_each(|(i, per_nonnative_bits)| {
                let mut val = vec![CF::zero(); params.num_limbs];
                let mut lc = vec![LinearCombination::<CF>::zero(); params.num_limbs];

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
                        // TODO (raychu86): Confirm linear combination is correct:
                        // lc[k] = &lc[k] + bit.lc() * lookup_table[j][k];

                        lc[k] = &lc[k] + bit.lc(CS::one(), CF::one()) * lookup_table[j][k];
                    }
                }

                let mut limbs = Vec::new();
                for k in 0..params.num_limbs {
                    let gadget =
                        AllocatedFp::alloc_input(cs.ns(|| format!("alloc_input_{}_{}", i, k)), || Ok(val[k])).unwrap();

                    // TODO (raychu86): Confirm linear combination subtraction is equivalent:
                    // lc[k] = lc[k] - (CF::one(), &gadget.variable);
                    match &gadget.variable {
                        ConstraintVariable::Var(var) => {
                            lc[k] = lc[k].clone() - (CF::one(), *var);
                        }
                        ConstraintVariable::LC(linear_combination) => {
                            lc[k] = &lc[k] - (CF::one(), linear_combination);
                        }
                    }

                    // TODO (raychu86): Confirm CS enforcement is equivalent:
                    // cs.enforce_constraint(lc!(), lc!(), lc[k].clone()).unwrap();
                    cs.enforce(
                        || format!("enforce_constraint_{}_{}", i, k),
                        |lc| lc,
                        |lc| lc,
                        |_| lc[k].clone(),
                    );

                    limbs.push(FpGadget::<CF>::from(gadget));
                }

                dest_gadgets.push(NonNativeFieldVar::<F, CF>::Var(AllocatedNonNativeFieldVar::<F, CF> {
                    limbs,
                    num_of_additions_over_normal_form: CF::zero(),
                    is_in_the_normal_form: true,
                    target_phantom: Default::default(),
                }));
            });

        Ok((dest_gadgets, dest_bits))
    }
}

impl<F: PrimeField, CF: PrimeField, PS: AlgebraicSponge<CF>, S: AlgebraicSpongeVar<CF, PS>>
    FiatShamirRngVar<F, CF, FiatShamirAlgebraicSpongeRng<F, CF, PS>> for FiatShamirAlgebraicSpongeRngVar<F, CF, PS, S>
{
    fn new<CS: ConstraintSystem<CF>>(cs: CS) -> Self {
        Self {
            s: S::new(cs),
            f_phantom: PhantomData,
            cf_phantom: PhantomData,
            ps_phantom: PhantomData,
        }
    }

    fn constant<CS: ConstraintSystem<CF>>(cs: CS, pfs: &FiatShamirAlgebraicSpongeRng<F, CF, PS>) -> Self {
        Self {
            s: S::constant(cs, &pfs.s.clone()),
            f_phantom: PhantomData,
            cf_phantom: PhantomData,
            ps_phantom: PhantomData,
        }
    }

    fn absorb_nonnative_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        elems: &[NonNativeFieldVar<F, CF>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError> {
        Self::push_gadgets_to_sponge(cs, &mut self.s, &elems.to_vec(), ty)
    }

    fn absorb_native_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        elems: &[FpGadget<CF>],
    ) -> Result<(), SynthesisError> {
        self.s.absorb(cs, elems)?;
        Ok(())
    }

    fn absorb_bytes<CS: ConstraintSystem<CF>>(&mut self, mut cs: CS, elems: &[UInt8]) -> Result<(), SynthesisError> {
        let capacity = CF::size_in_bits() - 1;
        let mut bits = Vec::<Boolean>::new();
        for elem in elems.iter() {
            let mut bits_le = elem.to_bits_le(); // UInt8's to_bits is le, which is an exception in Zexe.
            bits_le.reverse();
            bits.extend_from_slice(&bits_le);
        }

        let mut adjustment_factors = Vec::<CF>::new();
        let mut cur = CF::one();
        for _ in 0..capacity {
            adjustment_factors.push(cur);
            cur.double_in_place();
        }

        let mut gadgets = Vec::<FpGadget<CF>>::new();
        for (i, elem_bits) in bits.chunks(capacity).enumerate() {
            let mut elem = CF::zero();
            let mut lc = LinearCombination::zero();
            for (bit, adjustment_factor) in elem_bits.iter().rev().zip(adjustment_factors.iter()) {
                if bit.get_value().unwrap_or_default() {
                    elem += adjustment_factor;
                }
                // TODO (raychu86): Confirm linear combination is correct:
                // lc = &lc + bit.lc() * *adjustment_factor;

                lc = &lc + bit.lc(CS::one(), CF::one()) * *adjustment_factor;
            }

            let gadget = AllocatedFp::alloc_input(cs.ns(|| format!("alloc_input_{}", i)), || Ok(elem))?;

            // TODO (raychu86): Confirm linear combination subtraction is equivalent:
            // lc = lc.clone() - (CF::one(), gadget.variable);
            match &gadget.variable {
                ConstraintVariable::Var(var) => {
                    lc = lc.clone() - (CF::one(), *var);
                }
                ConstraintVariable::LC(linear_combination) => {
                    lc = &lc - (CF::one(), linear_combination);
                }
            }

            gadgets.push(FpGadget::from(gadget));

            // TODO (raychu86): Confirm CS enforcement is equivalent:
            // ccs.enforce_constraint(lc!(), lc!(), lc)?;
            cs.enforce(|| format!("enforce_constraint_{}", i), |lc| lc, |lc| lc, |_| lc);
        }

        self.s.absorb(cs.ns(|| "absorb"), &gadgets)
    }

    fn squeeze_native_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<FpGadget<CF>>, SynthesisError> {
        self.s.squeeze(cs, num)
    }

    fn squeeze_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError> {
        Self::get_gadgets_from_sponge(cs, &mut self.s, num, false)
    }

    #[allow(clippy::type_complexity)]
    fn squeeze_field_elements_and_bits<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<(Vec<NonNativeFieldVar<F, CF>>, Vec<Vec<Boolean>>), SynthesisError> {
        Self::get_gadgets_and_bits_from_sponge(cs, &mut self.s, num, false)
    }

    fn squeeze_128_bits_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError> {
        Self::get_gadgets_from_sponge(cs, &mut self.s, num, true)
    }

    #[allow(clippy::type_complexity)]
    fn squeeze_128_bits_field_elements_and_bits<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<(Vec<NonNativeFieldVar<F, CF>>, Vec<Vec<Boolean>>), SynthesisError> {
        Self::get_gadgets_and_bits_from_sponge(cs, &mut self.s, num, true)
    }
}
