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

use core::borrow::Borrow;

use snarkvm_curves::{AffineCurve, PairingCurve, PairingEngine};
use snarkvm_gadgets::{
    fields::FpGadget,
    traits::{alloc::AllocGadget, curves::PairingGadget, fields::FieldGadget},
    Boolean,
    CondSelectGadget,
    EqGadget,
    SumGadget,
};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use crate::{
    sonic_pc::{gadgets::verifier_key::VerifierKeyVar, PreparedVerifierKey, VerifierKey},
    Vec,
};
use snarkvm_algorithms::Prepare;

/// Var for the verification key of the Marlin-KZG10 polynomial commitment scheme.
#[allow(clippy::type_complexity)]
pub struct PreparedVerifierKeyVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> {
    /// Generator of G1.
    pub prepared_g: Vec<PG::G1Gadget>,
    /// The generator of G1 that is used for making a commitment hiding.
    pub prepared_gamma_g: Vec<PG::G1Gadget>,
    /// Generator of G2.
    pub prepared_h: PG::G2PreparedGadget,
    /// Generator of G1, times first monomial.
    pub prepared_beta_h: PG::G2PreparedGadget,
    /// Used for the shift powers associated with different degree bounds.
    pub degree_bounds_and_prepared_neg_powers_of_h:
        Option<Vec<(usize, FpGadget<<BaseCurve as PairingEngine>::Fr>, PG::G2PreparedGadget)>>,
    /// If not a constant allocation, the original vk is attached (for computing the shift power series)
    pub origin_vk: Option<VerifierKeyVar<TargetCurve, BaseCurve, PG>>,
}

impl<TargetCurve, BaseCurve, PG> PreparedVerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    /// Find the appropriate shift for the degree bound.
    pub fn get_prepared_shift_power<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
        bound: &FpGadget<<BaseCurve as PairingEngine>::Fr>,
    ) -> Result<PG::G2PreparedGadget, SynthesisError> {
        // Search the bound using PIR
        if self.degree_bounds_and_prepared_neg_powers_of_h.is_none() {
            return Err(SynthesisError::UnexpectedIdentity);
        } else {
            let degree_bounds_and_prepared_neg_powers_of_h =
                self.degree_bounds_and_prepared_neg_powers_of_h.clone().unwrap();

            let mut pir_vector = vec![false; degree_bounds_and_prepared_neg_powers_of_h.len()];

            let desired_bound_value = bound.get_value().unwrap_or_default();

            for (i, (_, this_bound, _)) in degree_bounds_and_prepared_neg_powers_of_h.iter().enumerate() {
                if this_bound.get_value().unwrap_or_default().eq(&desired_bound_value) {
                    pir_vector[i] = true;
                    break;
                }
            }

            let mut pir_vector_gadgets = Vec::with_capacity(pir_vector.len());
            for (i, bit) in pir_vector.iter().enumerate() {
                pir_vector_gadgets.push(Boolean::alloc(cs.ns(|| format!("alloc_pir_{}", i)), || Ok(bit))?);
            }

            // Sum of the PIR values are equal to one
            let mut sum = FpGadget::<<BaseCurve as PairingEngine>::Fr>::zero(cs.ns(|| "zero"))?;
            let one = FpGadget::<<BaseCurve as PairingEngine>::Fr>::one(cs.ns(|| "one"))?;
            for (i, pir_gadget) in pir_vector_gadgets.iter().enumerate() {
                let temp = FpGadget::<<BaseCurve as PairingEngine>::Fr>::from_boolean(
                    cs.ns(|| format!("from_boolean_{}", i)),
                    pir_gadget.clone(),
                )?;

                sum = sum.add(cs.ns(|| format!("sum_add_pir{}", i)), &temp)?;
            }
            sum.enforce_equal(cs.ns(|| "sum_enforce_equal"), &one)?;

            // PIR the value
            let zero_bound = FpGadget::<<BaseCurve as PairingEngine>::Fr>::zero(cs.ns(|| "zero_bound"))?;
            let zero_shift_power = PG::G2PreparedGadget::zero(cs.ns(|| "zero_shift_power"))?;
            let mut sum_bound = zero_bound.clone();
            let mut shift_powers_to_be_summed = Vec::new();

            for (i, (pir_gadget, (_, degree, shift_power))) in pir_vector_gadgets
                .iter()
                .zip(degree_bounds_and_prepared_neg_powers_of_h.iter())
                .enumerate()
            {
                let found_bound = FpGadget::<<BaseCurve as PairingEngine>::Fr>::conditionally_select(
                    cs.ns(|| format!("found_bound_cond_select{}", i)),
                    pir_gadget,
                    degree,
                    &zero_bound,
                )?;
                sum_bound.add_in_place(cs.ns(|| format!("update sum_bound{}", i)), &found_bound)?;

                let found_shift_power = PG::G2PreparedGadget::conditionally_select(
                    cs.ns(|| format!("found_shift_conditionally_select{}", i)),
                    pir_gadget,
                    shift_power,
                    &zero_shift_power,
                )?;

                shift_powers_to_be_summed.push(found_shift_power);
            }

            sum_bound.enforce_equal(cs.ns(|| "found_bound_enforce_equal"), &bound)?;

            let sum_shift_power =
                PG::G2PreparedGadget::sum(cs.ns(|| "sum the shift powers for PIR"), &shift_powers_to_be_summed)?;
            Ok(sum_shift_power)
        }
    }
}

impl<TargetCurve, BaseCurve, PG> Clone for PreparedVerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self {
            prepared_g: self.prepared_g.clone(),
            prepared_gamma_g: self.prepared_gamma_g.clone(),
            prepared_h: self.prepared_h.clone(),
            prepared_beta_h: self.prepared_beta_h.clone(),
            degree_bounds_and_prepared_neg_powers_of_h: self.degree_bounds_and_prepared_neg_powers_of_h.clone(),
            origin_vk: self.origin_vk.clone(),
        }
    }
}

impl<TargetCurve, BaseCurve, PG> Into<VerifierKeyVar<TargetCurve, BaseCurve, PG>>
    for PreparedVerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn into(self) -> VerifierKeyVar<TargetCurve, BaseCurve, PG> {
        match self.origin_vk {
            Some(vk) => vk.clone(),
            None => {
                eprintln!("Missing original vk");
                panic!()
            }
        }
    }
}

impl<TargetCurve, BaseCurve, PG> AllocGadget<PreparedVerifierKey<TargetCurve>, <BaseCurve as PairingEngine>::Fr>
    for PreparedVerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedVerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?.borrow().clone();

        let mut prepared_g = Vec::<PG::G1Gadget>::with_capacity(obj.prepared_vk.prepared_g.len());
        for (i, g) in obj.prepared_vk.prepared_g.iter().enumerate() {
            prepared_g.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_constant(cs.ns(|| format!("g_{}", i)), || {
                Ok(g.into_projective())
            })?);
        }

        let mut prepared_gamma_g = Vec::<PG::G1Gadget>::with_capacity(obj.prepared_vk.prepared_gamma_g.len());
        for (i, gamma_g) in obj.prepared_vk.prepared_gamma_g.iter().enumerate() {
            prepared_gamma_g.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_constant(
                cs.ns(|| format!("gamma_g_{}", i)), || Ok(gamma_g.into_projective())
            )?);
        }

        let prepared_h = PG::G2PreparedGadget::alloc(cs.ns(|| "prepared_h"), || Ok(&obj.prepared_vk.prepared_h))?;
        let prepared_beta_h =
            PG::G2PreparedGadget::alloc(cs.ns(|| "prepared_beta_h"), || Ok(&obj.prepared_vk.prepared_beta_h))?;

        let degree_bounds_and_prepared_neg_powers_of_h = if obj.degree_bounds_and_prepared_neg_powers_of_h.is_some() {
            let mut res = Vec::<(usize, FpGadget<<BaseCurve as PairingEngine>::Fr>, PG::G2PreparedGadget)>::new();

            for (i, (d, shift_power_elem)) in obj
                .degree_bounds_and_prepared_neg_powers_of_h
                .as_ref()
                .unwrap()
                .iter()
                .enumerate()
            {
                let gadget = <PG::G2PreparedGadget as AllocGadget<
                    <TargetCurve::G2Affine as PairingCurve>::Prepared,
                    <BaseCurve as PairingEngine>::Fr,
                >>::alloc_constant(
                    cs.ns(|| format!("alloc_constant_gadget_{}", i)),
                    || Ok(shift_power_elem),
                )?;

                let d_gadget = FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc_constant(
                    cs.ns(|| format!("alloc_constant_d_{}", i)),
                    || Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(*d as u128)),
                )?;

                res.push((*d, d_gadget, gadget));
            }
            Some(res)
        } else {
            None
        };

        Ok(Self {
            prepared_g,
            prepared_gamma_g,
            prepared_h,
            prepared_beta_h,
            degree_bounds_and_prepared_neg_powers_of_h,
            origin_vk: None,
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedVerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedVerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

impl<TargetCurve, BaseCurve, PG> AllocGadget<VerifierKey<TargetCurve>, <BaseCurve as PairingEngine>::Fr>
    for PreparedVerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?.borrow().clone();
        let pvk = VerifierKey::<TargetCurve>::prepare(&obj);
        <Self as AllocGadget<PreparedVerifierKey<TargetCurve>, <BaseCurve as PairingEngine>::Fr>>::alloc_constant(
            cs,
            || Ok(pvk),
        )
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use snarkvm_curves::{
        bls12_377::{Bls12_377, Fq},
        bw6_761::BW6_761,
    };
    use snarkvm_gadgets::{
        curves::bls12_377::PairingGadget as Bls12_377PairingGadget,
        traits::eq::EqGadget,
        PrepareGadget,
    };
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::rand::test_rng;

    use crate::{sonic_pc::SonicKZG10, PCUniversalParams, PolynomialCommitment};

    use super::*;
    use rand::Rng;
    use snarkvm_algorithms::Prepare;
    use snarkvm_fields::PrimeField;

    type PC = SonicKZG10<Bls12_377>;
    type PG = Bls12_377PairingGadget;
    type BaseCurve = BW6_761;

    const MAX_DEGREE: usize = 383;
    const SUPPORTED_DEGREE: usize = 300;
    const SUPPORTED_HIDING_BOUND: usize = 1;

    // TODO (raychu86): Implement `test_to_constraint_field`.

    #[test]
    fn test_alloc() {
        let rng = &mut test_rng();

        let cs = &mut TestConstraintSystem::<Fq>::new();

        // Construct the universal params.
        let pp = PC::setup(MAX_DEGREE, rng).unwrap();

        // Construct the verifying key.
        let (_committer_key, vk) = PC::trim(&pp, SUPPORTED_DEGREE, SUPPORTED_HIDING_BOUND, None).unwrap();

        let prepared_vk = vk.prepare();

        // Allocate the prepared vk gadget.
        let prepared_vk_gadget =
            PreparedVerifierKeyVar::<_, BaseCurve, PG>::alloc_constant(cs.ns(|| "alloc_prepared_vk"), || {
                Ok(prepared_vk.clone())
            })
            .unwrap();

        // Gadget enforcement checks.
        let prepared_h_gadget =
            <PG as PairingGadget<_, _>>::G2PreparedGadget::alloc(cs.ns(|| "alloc_prepared_native_h"), || {
                Ok(&prepared_vk.prepared_vk.prepared_h)
            })
            .unwrap();
        let prepared_beta_h_gadget =
            <PG as PairingGadget<_, _>>::G2PreparedGadget::alloc(cs.ns(|| "alloc_native_prepared_beta_h"), || {
                Ok(&prepared_vk.prepared_vk.prepared_beta_h)
            })
            .unwrap();

        for (i, (g_element, g_gadget_element)) in prepared_vk
            .prepared_vk
            .prepared_g
            .iter()
            .zip(prepared_vk_gadget.prepared_g)
            .enumerate()
        {
            let prepared_g_gadget = <PG as PairingGadget<_, _>>::G1Gadget::alloc(
                cs.ns(|| format!("alloc_native_prepared_g_{}", i)),
                || Ok(g_element.into_projective()),
            )
            .unwrap();

            prepared_g_gadget
                .enforce_equal(cs.ns(|| format!("enforce_equals_prepared_g_{}", i)), &g_gadget_element)
                .unwrap();
        }

        prepared_h_gadget
            .enforce_equal(cs.ns(|| "enforce_equals_prepared_h"), &prepared_vk_gadget.prepared_h)
            .unwrap();
        prepared_beta_h_gadget
            .enforce_equal(
                cs.ns(|| "enforce_equals_prepared_beta_h"),
                &prepared_vk_gadget.prepared_beta_h,
            )
            .unwrap();

        // Native check that degree bounds are equivalent.

        assert_eq!(
            prepared_vk.degree_bounds_and_prepared_neg_powers_of_h.is_some(),
            prepared_vk_gadget.degree_bounds_and_prepared_neg_powers_of_h.is_some()
        );

        if let (Some(native), Some(gadget)) = (
            &prepared_vk.degree_bounds_and_prepared_neg_powers_of_h,
            &prepared_vk_gadget.degree_bounds_and_prepared_neg_powers_of_h,
        ) {
            // Check each degree bound and shift power.
            for (i, ((native_degree_bounds, native_shift_power), (degree_bounds, _fp_gadget, shift_power))) in
                native.iter().zip(gadget).enumerate()
            {
                assert_eq!(native_degree_bounds, degree_bounds);

                let shift_power_gadget = <PG as PairingGadget<_, _>>::G2PreparedGadget::alloc(
                    cs.ns(|| format!("alloc_native_shift_power_{}", i)),
                    || Ok(native_shift_power),
                )
                .unwrap();

                shift_power_gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equals_shift_power_{}", i)), shift_power)
                    .unwrap();
            }
        }

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_prepare() {
        let rng = &mut test_rng();

        let cs = &mut TestConstraintSystem::<Fq>::new();

        // Construct the universal params.
        let pp = PC::setup(MAX_DEGREE, rng).unwrap();

        // Construct the verifying key.
        let (_committer_key, vk) = PC::trim(&pp, SUPPORTED_DEGREE, SUPPORTED_HIDING_BOUND, None).unwrap();

        // Allocate the vk gadget.
        let vk_gadget = VerifierKeyVar::<_, BaseCurve, PG>::alloc(cs.ns(|| "alloc_vk"), || Ok(vk.clone())).unwrap();

        // Allocate the prepared vk gadget.
        let prepared_vk = vk.prepare();
        let expected_prepared_vk_gadget =
            PreparedVerifierKeyVar::<_, BaseCurve, PG>::alloc_constant(cs.ns(|| "alloc_prepared_vk"), || {
                Ok(prepared_vk.clone())
            })
            .unwrap();

        let prepared_vk_gadget = vk_gadget.prepare(cs.ns(|| "prepare")).unwrap();

        // Enforce that the elements are equivalent.

        for (i, (expected_g_element, g_element_gadget)) in expected_prepared_vk_gadget
            .prepared_g
            .iter()
            .zip(prepared_vk_gadget.prepared_g)
            .enumerate()
        {
            g_element_gadget
                .enforce_equal(
                    cs.ns(|| format!("enforce_equals_prepared_g_{}", i)),
                    &expected_g_element,
                )
                .unwrap();
        }

        assert_eq!(
            prepared_vk.degree_bounds_and_prepared_neg_powers_of_h.is_some(),
            prepared_vk_gadget.degree_bounds_and_prepared_neg_powers_of_h.is_some()
        );

        if let (Some(expected), Some(gadget)) = (
            &expected_prepared_vk_gadget.degree_bounds_and_prepared_neg_powers_of_h,
            &prepared_vk_gadget.degree_bounds_and_prepared_neg_powers_of_h,
        ) {
            // Check each degree bound and shift power.
            for (
                i,
                (
                    (expected_degree_bounds, expected_fp_gadget, expected_shift_power),
                    (degree_bounds, fp_gadget, shift_power),
                ),
            ) in expected.iter().zip(gadget).take(1).enumerate()
            {
                assert_eq!(expected_degree_bounds, degree_bounds);

                fp_gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equals_fp_gadget_{}", i)), &expected_fp_gadget)
                    .unwrap();

                println!(
                    "expected_degree_bounds {}, degree_bounds: {}",
                    expected_degree_bounds, degree_bounds
                );

                shift_power
                    .enforce_equal(
                        cs.ns(|| format!("enforce_equals_shift_power_{}", i)),
                        &expected_shift_power,
                    )
                    .unwrap();
            }
        }

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_get_prepared_shift_power() {
        let rng = &mut test_rng();

        let cs = &mut TestConstraintSystem::<Fq>::new();

        // Construct the universal params.
        let pp = PC::setup(MAX_DEGREE, rng).unwrap();

        // Establish the bound
        let supported_degree_bounds = pp.supported_degree_bounds();
        let bound = supported_degree_bounds[rng.gen_range(0..supported_degree_bounds.len())];

        let bound_field = <BaseCurve as PairingEngine>::Fr::from_repr(
            <<BaseCurve as PairingEngine>::Fr as PrimeField>::BigInteger::from(bound as u64),
        )
        .unwrap();
        let bound_gadget = FpGadget::alloc(cs.ns(|| "alloc_bound"), || Ok(bound_field)).unwrap();

        // Construct the verifying key.
        let (_committer_key, vk) = PC::trim(&pp, SUPPORTED_DEGREE, SUPPORTED_HIDING_BOUND, Some(&vec![bound])).unwrap();
        let pvk = vk.prepare();

        // Allocate the vk gadget.
        let pvk_gadget =
            PreparedVerifierKeyVar::<_, BaseCurve, PG>::alloc_constant(cs.ns(|| "alloc_pvk"), || Ok(pvk.clone()))
                .unwrap();

        assert!(pvk.degree_bounds_and_prepared_neg_powers_of_h.is_some());
        assert!(pvk_gadget.degree_bounds_and_prepared_neg_powers_of_h.is_some());

        let prepared_shift_power = pvk_gadget
            .get_prepared_shift_power(cs.ns(|| "get_shift_power"), &bound_gadget)
            .unwrap();
        let expected_shift_power =
            <PG as PairingGadget<_, _>>::G2PreparedGadget::alloc(cs.ns(|| "allocate_native_shift_power"), || {
                Ok(pvk.get_prepared_shift_power(bound).unwrap())
            })
            .unwrap();

        prepared_shift_power
            .enforce_equal(cs.ns(|| "enforce_equals_shift_power"), &expected_shift_power)
            .unwrap();

        assert!(cs.is_satisfied());
    }
}
