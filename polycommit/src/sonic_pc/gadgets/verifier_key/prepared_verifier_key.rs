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
};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use crate::{
    sonic_pc::{gadgets::verifier_key::VerifierKeyVar, PreparedVerifierKey},
    Vec,
};

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
    /// Indicate whether or not it is a constant allocation (which decides whether or not shift powers are precomputed)
    pub constant_allocation: bool,
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
    ) -> Option<PG::G2PreparedGadget> {
        if self.constant_allocation {
            if self.degree_bounds_and_prepared_neg_powers_of_h.is_none() {
                None
            } else {
                let degree_bounds_and_prepared_neg_powers_of_h =
                    self.degree_bounds_and_prepared_neg_powers_of_h.as_ref().unwrap();
                let bound_value = bound.get_value().unwrap_or_default();

                for (_, bound, prepared_shift_power) in degree_bounds_and_prepared_neg_powers_of_h.iter() {
                    if bound.get_value().unwrap_or_default() == bound_value {
                        return Some((*prepared_shift_power).clone());
                    }
                }

                None
            }
        } else {
            let shift_power = self
                .origin_vk
                .as_ref()
                .unwrap()
                .get_shift_power(cs.ns(|| "get_shift_power"), bound);

            if let Some(shift_power) = shift_power {
                let prepared_shift_gadget = PG::prepare_g2(cs.ns(|| "prepare the shift power"), shift_power).ok()?;
                Some(prepared_shift_gadget)
            } else {
                None
            }
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
            constant_allocation: self.constant_allocation,
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

        let mut prepared_g = Vec::<PG::G1Gadget>::new();
        for (i, g) in obj.prepared_vk.prepared_g.iter().enumerate() {
            prepared_g.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_constant(cs.ns(|| format!("g_{}", i)), || {
                Ok(g.into_projective())
            })?);
        }

        let mut prepared_gamma_g = Vec::<PG::G1Gadget>::new();
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
            constant_allocation: true,
            origin_vk: None,
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedVerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?.borrow().clone();

        let mut prepared_g = Vec::<PG::G1Gadget>::new();
        for (i, g) in obj.prepared_vk.prepared_g.iter().enumerate() {
            prepared_g.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc(cs.ns(|| format!("g_{}", i)), || {
                Ok(g.into_projective())
            })?);
        }

        let mut prepared_gamma_g = Vec::<PG::G1Gadget>::new();
        for (i, gamma_g) in obj.prepared_vk.prepared_gamma_g.iter().enumerate() {
            prepared_gamma_g.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc(cs.ns(|| format!("gamma_g_{}", i)), || {
                Ok(gamma_g.into_projective())
            })?);
        }

        let prepared_h = PG::G2PreparedGadget::alloc(cs.ns(|| "h"), || Ok(&obj.prepared_vk.prepared_h))?;
        let prepared_beta_h = PG::G2PreparedGadget::alloc(cs.ns(|| "beta_h"), || Ok(&obj.prepared_vk.prepared_beta_h))?;

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
                >>::alloc(cs.ns(|| format!("alloc_constant_gadget_{}", i)), || {
                    Ok(shift_power_elem)
                })?;

                let d_gadget =
                    FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc(cs.ns(|| format!("alloc_d_{}", i)), || {
                        Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(*d as u128))
                    })?;

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
            constant_allocation: true,
            origin_vk: None,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedVerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?.borrow().clone();

        let mut prepared_g = Vec::<PG::G1Gadget>::new();
        for (i, g) in obj.prepared_vk.prepared_g.iter().enumerate() {
            prepared_g.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_input(cs.ns(|| format!("g_{}", i)), || {
                Ok(g.into_projective())
            })?);
        }

        let mut prepared_gamma_g = Vec::<PG::G1Gadget>::new();
        for (i, gamma_g) in obj.prepared_vk.prepared_gamma_g.iter().enumerate() {
            prepared_gamma_g.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_input(cs.ns(|| format!("gamma_g_{}", i)), || {
                Ok(gamma_g.into_projective())
            })?);
        }

        let prepared_h = PG::G2PreparedGadget::alloc_input(cs.ns(|| "h"), || Ok(&obj.prepared_vk.prepared_h))?;
        let prepared_beta_h =
            PG::G2PreparedGadget::alloc_input(cs.ns(|| "beta_h"), || Ok(&obj.prepared_vk.prepared_beta_h))?;

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
                >>::alloc_input(cs.ns(|| format!("alloc_constant_gadget_{}", i)), || {
                    Ok(shift_power_elem)
                })?;

                let d_gadget = FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc_input(
                    cs.ns(|| format!("alloc_input_d_{}", i)),
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
            constant_allocation: true,
            origin_vk: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use snarkvm_curves::{
        bls12_377::{Bls12_377, Fq},
        bw6_761::BW6_761,
        ProjectiveCurve,
    };
    use snarkvm_gadgets::{
        curves::bls12_377::PairingGadget as Bls12_377PairingGadget,
        traits::eq::EqGadget,
        PrepareGadget,
    };
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::rand::test_rng;

    use crate::{sonic_pc::SonicKZG10, PolynomialCommitment};

    use super::*;
    use snarkvm_algorithms::Prepare;

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
        let prepared_vk_gadget = PreparedVerifierKeyVar::<_, BaseCurve, PG>::alloc(
            cs.ns(|| "alloc_prepared_vk"),
            || Ok(prepared_vk.clone()),
        )
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
            for (i, ((native_degree_bounds, native_shift_powers), (degree_bounds, _fp_gadget, shift_powers))) in
                native.iter().zip(gadget).enumerate()
            {
                assert_eq!(native_degree_bounds, degree_bounds);

                for (j, (native_shift_power, shift_power)) in native_shift_powers.iter().zip(shift_powers).enumerate() {
                    assert_eq!(native_shift_power, &shift_power.get_value().unwrap().into_affine());

                    let shift_power_gadget = <PG as PairingGadget<_, _>>::G2Gadget::alloc(
                        cs.ns(|| format!("alloc_native_shift_power_{}_{}", i, j)),
                        || Ok(native_shift_power.into_projective()),
                    )
                    .unwrap();

                    shift_power_gadget
                        .enforce_equal(
                            cs.ns(|| format!("enforce_equals_shift_power_{}_{}", i, j)),
                            &shift_power,
                        )
                        .unwrap();
                }
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
        let expected_prepared_vk_gadget = PreparedVerifierKeyVar::<_, BaseCurve, PG>::alloc(
            cs.ns(|| "alloc_prepared_vk"),
            || Ok(prepared_vk.clone()),
        )
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
                    (expected_degree_bounds, expected_fp_gadget, expected_shift_powers),
                    (degree_bounds, fp_gadget, shift_powers),
                ),
            ) in expected.iter().zip(gadget).enumerate()
            {
                assert_eq!(expected_degree_bounds, degree_bounds);

                fp_gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equals_fp_gadget_{}", i)), &expected_fp_gadget)
                    .unwrap();

                for (j, (expected_shift_power, shift_power)) in
                    expected_shift_powers.iter().zip(shift_powers).enumerate()
                {
                    assert_eq!(
                        expected_shift_power.get_value().unwrap().into_affine(),
                        shift_power.get_value().unwrap().into_affine()
                    );

                    shift_power
                        .enforce_equal(
                            cs.ns(|| format!("enforce_equals_shift_power_{}_{}", i, j)),
                            &expected_shift_power,
                        )
                        .unwrap();
                }
            }
        }

        assert!(cs.is_satisfied());
    }
}
