use crate::{
    constraints::{
        EvaluationsVar,
        LabeledPointVar,
        LinearCombinationCoeffVar,
        LinearCombinationVar,
        PCCheckRandomDataVar,
        PCCheckVar,
        PrepareGadget,
        QuerySetVar,
    },
    data_structures::LabeledCommitment,
    kzg10::{Proof, VerifierKey as KZG10VerifierKey},
    marlin_pc::{
        data_structures::{Commitment, VerifierKey},
        MarlinKZG10,
        PreparedCommitment,
        PreparedVerifierKey,
    },
    BTreeMap,
    BTreeSet,
    BatchLCProof,
    String,
    ToString,
    Vec,
};
use snarkvm_curves::traits::PairingEngine;
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_gadgets::{
    fields::FpGadget,
    traits::{
        curves::{GroupGadget, PairingGadget},
        fields::{FieldGadget, ToConstraintFieldGadget},
        utilities::{boolean::Boolean, eq::EqGadget, ToBitsLEGadget, ToBytesGadget},
    },
    utilities::{alloc::AllocGadget, select::CondSelectGadget, uint::UInt8},
};
use snarkvm_nonnative::{NonNativeFieldMulResultVar, NonNativeFieldVar};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use core::{borrow::Borrow, convert::TryInto, ops::MulAssign};
use snarkvm_curves::AffineCurve;
use std::marker::PhantomData;

/// Var for the verification key of the Marlin-KZG10 polynomial commitment scheme.
#[allow(clippy::type_complexity)]
pub struct VerifierKeyVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    /// Generator of G1.
    pub g: PG::G1Gadget,
    /// Generator of G2.
    pub h: PG::G2Gadget,
    /// Generator of G1, times first monomial.
    pub beta_h: PG::G2Gadget,
    /// Used for the shift powers associated with different degree bounds.
    pub degree_bounds_and_shift_powers: Option<Vec<(usize, FpGadget<<BaseCurve as PairingEngine>::Fr>, PG::G1Gadget)>>,
}

impl<TargetCurve, BaseCurve, PG> VerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    /// Find the appropriate shift for the degree bound.
    pub fn get_shift_power<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
        bound: &FpGadget<<BaseCurve as PairingEngine>::Fr>,
    ) -> Option<PG::G1Gadget> {
        // Search the bound using PIR
        if self.degree_bounds_and_shift_powers.is_none() {
            None
        } else {
            let degree_bounds_and_shift_powers = self.degree_bounds_and_shift_powers.clone().unwrap();

            let mut pir_vector = vec![false; degree_bounds_and_shift_powers.len()];

            let desired_bound_value = bound.get_value().unwrap_or_default();

            for (i, (_, this_bound, _)) in degree_bounds_and_shift_powers.iter().enumerate() {
                if this_bound.get_value().unwrap_or_default().eq(&desired_bound_value) {
                    pir_vector[i] = true;
                    break;
                }
            }

            let mut pir_vector_gadgets = Vec::new();
            for (i, bit) in pir_vector.iter().enumerate() {
                pir_vector_gadgets.push(Boolean::alloc(cs.ns(|| format!("alloc_pir_{}", i)), || Ok(bit)).unwrap());
            }

            // Sum of the PIR values are equal to one
            let mut sum = FpGadget::<<BaseCurve as PairingEngine>::Fr>::zero(cs.ns(|| "zero")).unwrap();
            let one = FpGadget::<<BaseCurve as PairingEngine>::Fr>::one(cs.ns(|| "one")).unwrap();
            for (i, pir_gadget) in pir_vector_gadgets.iter().enumerate() {
                let temp = FpGadget::<<BaseCurve as PairingEngine>::Fr>::from_boolean(
                    cs.ns(|| format!("from_boolean_{}", i)),
                    pir_gadget.clone(),
                )
                .unwrap();

                sum = sum.add(cs.ns(|| format!("sum_add_pir{}", i)), &temp).unwrap();
            }
            sum.enforce_equal(cs.ns(|| "sum_enforce_equal"), &one).unwrap();

            // PIR the value
            let mut found_bound =
                FpGadget::<<BaseCurve as PairingEngine>::Fr>::zero(cs.ns(|| "found_bound_zero")).unwrap();

            let mut found_shift_power = PG::G1Gadget::zero(cs.ns(|| "found_shift_power_zero")).unwrap();

            for (i, (pir_gadget, (_, degree, shift_power))) in pir_vector_gadgets
                .iter()
                .zip(degree_bounds_and_shift_powers.iter())
                .enumerate()
            {
                found_bound = FpGadget::<<BaseCurve as PairingEngine>::Fr>::conditionally_select(
                    cs.ns(|| format!("found_bound_coond_select{}", i)),
                    pir_gadget,
                    degree,
                    &found_bound,
                )
                .unwrap();

                found_shift_power = PG::G1Gadget::conditionally_select(
                    cs.ns(|| format!("found_shift_conditionally_select+{}", i)),
                    pir_gadget,
                    shift_power,
                    &found_shift_power,
                )
                .unwrap();
            }

            found_bound
                .enforce_equal(cs.ns(|| "found_bound_enforce_equal"), &bound)
                .unwrap();

            Some(found_shift_power)
        }
    }
}

impl<TargetCurve, BaseCurve, PG> Clone for VerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self {
            g: self.g.clone(),
            h: self.h.clone(),
            beta_h: self.beta_h.clone(),
            degree_bounds_and_shift_powers: self.degree_bounds_and_shift_powers.clone(),
        }
    }
}

impl<TargetCurve, BaseCurve, PG> AllocGadget<VerifierKey<TargetCurve>, <BaseCurve as PairingEngine>::Fr>
    for VerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let vk_orig = value_gen()?.borrow().clone();

        let VerifierKey {
            vk,
            degree_bounds_and_shift_powers,
            ..
        } = vk_orig;

        let degree_bounds_and_shift_powers = degree_bounds_and_shift_powers.map(|vec| {
            vec.iter()
                .enumerate()
                .map(|(i, (s, g))| {
                    (
                        *s,
                        FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc_constant(
                            cs.ns(|| format!("degree bound_{}", i)),
                            || Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(*s as u128)),
                        )
                        .unwrap(),
                        PG::G1Gadget::alloc_constant(cs.ns(|| format!("pow_{}", i)), || Ok(g.into_projective()))
                            .unwrap(),
                    )
                })
                .collect()
        });

        let KZG10VerifierKey { g, h, beta_h, .. } = vk;

        let g = PG::G1Gadget::alloc_constant(cs.ns(|| "g"), || Ok(g.into_projective()))?;
        let h = PG::G2Gadget::alloc_constant(cs.ns(|| "h"), || Ok(h.into_projective()))?;
        let beta_h = PG::G2Gadget::alloc_constant(cs.ns(|| "beta_h"), || Ok(beta_h.into_projective()))?;

        Ok(Self {
            g,
            h,
            beta_h,
            degree_bounds_and_shift_powers,
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let vk_orig = value_gen()?.borrow().clone();

        let VerifierKey {
            vk,
            degree_bounds_and_shift_powers,
            ..
        } = vk_orig;

        let degree_bounds_and_shift_powers = degree_bounds_and_shift_powers.map(|vec| {
            vec.iter()
                .enumerate()
                .map(|(i, (s, g))| {
                    (
                        *s,
                        FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc(
                            cs.ns(|| format!("degree bound_{}", i)),
                            || Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(*s as u128)),
                        )
                        .unwrap(),
                        PG::G1Gadget::alloc(cs.ns(|| format!("pow_{}", i)), || Ok(g.into_projective())).unwrap(),
                    )
                })
                .collect()
        });

        let KZG10VerifierKey { g, h, beta_h, .. } = vk;

        let g = PG::G1Gadget::alloc(cs.ns(|| "g"), || Ok(g.into_projective()))?;
        let h = PG::G2Gadget::alloc(cs.ns(|| "h"), || Ok(h.into_projective()))?;
        let beta_h = PG::G2Gadget::alloc(cs.ns(|| "beta_h"), || Ok(beta_h.into_projective()))?;

        Ok(Self {
            g,
            h,
            beta_h,
            degree_bounds_and_shift_powers,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let vk_orig = value_gen()?.borrow().clone();

        let VerifierKey {
            vk,
            degree_bounds_and_shift_powers,
            ..
        } = vk_orig;

        let degree_bounds_and_shift_powers = degree_bounds_and_shift_powers.map(|vec| {
            vec.iter()
                .enumerate()
                .map(|(i, (s, g))| {
                    (
                        *s,
                        FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc_input(
                            cs.ns(|| format!("degree bound_{}", i)),
                            || Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(*s as u128)),
                        )
                        .unwrap(),
                        PG::G1Gadget::alloc_input(cs.ns(|| format!("pow_{}", i)), || Ok(g.into_projective())).unwrap(),
                    )
                })
                .collect()
        });

        let KZG10VerifierKey { g, h, beta_h, .. } = vk;

        let g = PG::G1Gadget::alloc_input(cs.ns(|| "g"), || Ok(g.into_projective()))?;
        let h = PG::G2Gadget::alloc_input(cs.ns(|| "h"), || Ok(h.into_projective()))?;
        let beta_h = PG::G2Gadget::alloc_input(cs.ns(|| "beta_h"), || Ok(beta_h.into_projective()))?;

        Ok(Self {
            g,
            h,
            beta_h,
            degree_bounds_and_shift_powers,
        })
    }
}

impl<TargetCurve, BaseCurve, PG> ToBytesGadget<<BaseCurve as PairingEngine>::Fr>
    for VerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn to_bytes<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        let mut bytes = Vec::new();

        bytes.extend_from_slice(&self.g.to_bytes(cs.ns(|| "g_to_bytes"))?);
        bytes.extend_from_slice(&self.h.to_bytes(cs.ns(|| "h_to_bytes"))?);
        bytes.extend_from_slice(&self.beta_h.to_bytes(cs.ns(|| "beta_h_to_bytes"))?);

        if self.degree_bounds_and_shift_powers.is_some() {
            let degree_bounds_and_shift_powers = self.degree_bounds_and_shift_powers.as_ref().unwrap();
            for (i, (_, degree_bound, shift_power)) in degree_bounds_and_shift_powers.iter().enumerate() {
                bytes.extend_from_slice(&degree_bound.to_bytes(cs.ns(|| format!("degree_bound_to_bytes_{}", i)))?);
                bytes.extend_from_slice(&shift_power.to_bytes(cs.ns(|| format!("shift_power_to_bytes_{}", i)))?);
            }
        }

        Ok(bytes)
    }

    fn to_bytes_strict<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

impl<TargetCurve, BaseCurve, PG> ToConstraintFieldGadget<<BaseCurve as PairingEngine>::Fr>
    for VerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    PG::G1Gadget: ToConstraintFieldGadget<<BaseCurve as PairingEngine>::Fr>,
    PG::G2Gadget: ToConstraintFieldGadget<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn to_constraint_field(&self) -> Result<Vec<FpGadget<<BaseCurve as PairingEngine>::Fr>>, SynthesisError> {
        let mut res = Vec::new();

        let mut g_gadget = self.g.to_constraint_field()?;
        let mut h_gadget = self.h.to_constraint_field()?;
        let mut beta_h_gadget = self.beta_h.to_constraint_field()?;

        res.append(&mut g_gadget);
        res.append(&mut h_gadget);
        res.append(&mut beta_h_gadget);

        if self.degree_bounds_and_shift_powers.as_ref().is_some() {
            let list = self.degree_bounds_and_shift_powers.as_ref().unwrap();
            for (_, d_gadget, shift_power) in list.iter() {
                let mut d_elems = vec![*d_gadget];
                let mut shift_power_elems = shift_power.to_constraint_field()?;

                res.append(&mut d_elems);
                res.append(&mut shift_power_elems);
            }
        }

        Ok(res)
    }
}

/// Var for the verification key of the Marlin-KZG10 polynomial commitment scheme.
#[allow(clippy::type_complexity)]
pub struct PreparedVerifierKeyVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    /// Generator of G1.
    pub prepared_g: Vec<PG::G1Gadget>,
    /// Generator of G2.
    pub prepared_h: PG::G2PreparedGadget,
    /// Generator of G1, times first monomial.
    pub prepared_beta_h: PG::G2PreparedGadget,
    /// Used for the shift powers associated with different degree bounds.
    pub prepared_degree_bounds_and_shift_powers:
        Option<Vec<(usize, FpGadget<<BaseCurve as PairingEngine>::Fr>, Vec<PG::G1Gadget>)>>,
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
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    /// Find the appropriate shift for the degree bound.
    pub fn get_shift_power<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
        bound: &FpGadget<<BaseCurve as PairingEngine>::Fr>,
    ) -> Option<Vec<PG::G1Gadget>> {
        if self.constant_allocation {
            if self.prepared_degree_bounds_and_shift_powers.is_none() {
                None
            } else {
                let prepared_degree_bounds_and_shift_powers =
                    self.prepared_degree_bounds_and_shift_powers.as_ref().unwrap();
                let bound_value = bound.get_value().unwrap_or_default();

                for (_, bound, prepared_shift_powers) in prepared_degree_bounds_and_shift_powers.iter() {
                    if bound.get_value().unwrap_or_default() == bound_value {
                        return Some((*prepared_shift_powers).clone());
                    }
                }

                None
            }
        } else {
            let shift_power = self.origin_vk.as_ref().unwrap().get_shift_power(cs, bound);

            if let Some(shift_power) = shift_power {
                let mut prepared_shift_gadgets = Vec::<PG::G1Gadget>::new();

                let supported_bits = <TargetCurve as PairingEngine>::Fr::size_in_bits();

                let mut cur: PG::G1Gadget = shift_power;
                for i in 0..supported_bits {
                    prepared_shift_gadgets.push(cur.clone());
                    cur.double_in_place(cs.ns(|| format!("cur_double_in_place_{}", i)))
                        .unwrap();
                }

                Some(prepared_shift_gadgets)
            } else {
                None
            }
        }
    }
}

impl<TargetCurve, BaseCurve, PG>
    PrepareGadget<VerifierKeyVar<TargetCurve, BaseCurve, PG>, <BaseCurve as PairingEngine>::Fr>
    for PreparedVerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn prepare<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        mut cs: CS,
        unprepared: &VerifierKeyVar<TargetCurve, BaseCurve, PG>,
    ) -> Result<Self, SynthesisError> {
        let supported_bits = <<TargetCurve as PairingEngine>::Fr as PrimeField>::size_in_bits();
        let mut prepared_g = Vec::<PG::G1Gadget>::new();

        let mut g: PG::G1Gadget = unprepared.g.clone();
        for i in 0..supported_bits {
            prepared_g.push(g.clone());
            g.double_in_place(cs.ns(|| format!("double_in_place_{}", i)))?;
        }

        let prepared_h = PG::prepare_g2(cs.ns(|| "prepared_h"), unprepared.h.clone())?;
        let prepared_beta_h = PG::prepare_g2(cs.ns(|| "prepared_beta_h"), unprepared.beta_h.clone())?;

        let prepared_degree_bounds_and_shift_powers = if unprepared.degree_bounds_and_shift_powers.is_some() {
            let mut res = Vec::<(usize, FpGadget<<BaseCurve as PairingEngine>::Fr>, Vec<PG::G1Gadget>)>::new();

            for (d, d_gadget, shift_power) in unprepared.degree_bounds_and_shift_powers.as_ref().unwrap().iter() {
                res.push((*d, (*d_gadget).clone(), vec![shift_power.clone()]));
            }

            Some(res)
        } else {
            None
        };

        Ok(Self {
            prepared_g,
            prepared_h,
            prepared_beta_h,
            prepared_degree_bounds_and_shift_powers,
            constant_allocation: false,
            origin_vk: Some(unprepared.clone()),
        })
    }
}

impl<TargetCurve, BaseCurve, PG> Clone for PreparedVerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self {
            prepared_g: self.prepared_g.clone(),
            prepared_h: self.prepared_h.clone(),
            prepared_beta_h: self.prepared_beta_h.clone(),
            prepared_degree_bounds_and_shift_powers: self.prepared_degree_bounds_and_shift_powers.clone(),
            constant_allocation: self.constant_allocation,
            origin_vk: self.origin_vk.clone(),
        }
    }
}

impl<TargetCurve, BaseCurve, PG> AllocGadget<PreparedVerifierKey<TargetCurve>, <BaseCurve as PairingEngine>::Fr>
    for PreparedVerifierKeyVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedVerifierKey<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?.borrow();

        let mut prepared_g = Vec::<PG::G1Gadget>::new();
        for (i, g) in obj.prepared_vk.prepared_g.iter().enumerate() {
            prepared_g.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_constant(cs.ns(|| format!("g_{}", i)), || {
                Ok(g.into_projective())
            })?);
        }

        let prepared_h = PG::G2PreparedGadget::alloc(cs.ns(|| "prepared_h"), || Ok(&obj.prepared_vk.prepared_h))?;
        let prepared_beta_h =
            PG::G2PreparedGadget::alloc(cs.ns(|| "prepared_beta_h"), || Ok(&obj.prepared_vk.prepared_beta_h))?;

        let prepared_degree_bounds_and_shift_powers = if obj.prepared_degree_bounds_and_shift_powers.is_some() {
            let mut res = Vec::<(usize, FpGadget<<BaseCurve as PairingEngine>::Fr>, Vec<PG::G1Gadget>)>::new();

            for (i, (d, shift_power_elems)) in obj
                .prepared_degree_bounds_and_shift_powers
                .as_ref()
                .unwrap()
                .iter()
                .enumerate()
            {
                let mut gadgets = Vec::<PG::G1Gadget>::new();
                for (j, shift_power_elem) in shift_power_elems.iter().enumerate() {
                    gadgets.push(<PG::G1Gadget as AllocGadget<
                        <TargetCurve as PairingEngine>::G1Projective,
                        <BaseCurve as PairingEngine>::Fr,
                    >>::alloc_constant(
                        cs.ns(|| format!("alloc_constant_gadget_{}_{}", i, j)),
                        || Ok(shift_power_elem.into_projective()),
                    )?);
                }

                let d_gadget = FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc(
                    cs.ns(|| format!("alloc_constant_d_{}", i)),
                    || Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(*d as u128)),
                )?;

                res.push((*d, d_gadget, gadgets));
            }
            Some(res)
        } else {
            None
        };

        Ok(Self {
            prepared_g,
            prepared_h,
            prepared_beta_h,
            prepared_degree_bounds_and_shift_powers,
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
        let obj = value_gen()?.borrow();

        let mut prepared_g = Vec::<PG::G1Gadget>::new();
        for (i, g) in obj.prepared_vk.prepared_g.iter().enumerate() {
            prepared_g.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc(cs.ns(|| format!("g_{}", i)), || {
                Ok(g.into_projective())
            })?);
        }

        let prepared_h = PG::G2PreparedGadget::alloc(cs.ns(|| "h"), || Ok(&obj.prepared_vk.prepared_h))?;
        let prepared_beta_h = PG::G2PreparedGadget::alloc(cs.ns(|| "beta_h"), || Ok(&obj.prepared_vk.prepared_beta_h))?;

        let prepared_degree_bounds_and_shift_powers = if obj.prepared_degree_bounds_and_shift_powers.is_some() {
            let mut res = Vec::<(usize, FpGadget<<BaseCurve as PairingEngine>::Fr>, Vec<PG::G1Gadget>)>::new();

            for (i, (d, shift_power_elems)) in obj
                .prepared_degree_bounds_and_shift_powers
                .as_ref()
                .unwrap()
                .iter()
                .enumerate()
            {
                let mut gadgets = Vec::<PG::G1Gadget>::new();
                for (j, shift_power_elem) in shift_power_elems.iter().enumerate() {
                    gadgets.push(<PG::G1Gadget as AllocGadget<
                        <TargetCurve as PairingEngine>::G1Projective,
                        <BaseCurve as PairingEngine>::Fr,
                    >>::alloc(
                        cs.ns(|| format!("alloc_gadget_{}_{}", i, j)),
                        || Ok(shift_power_elem.into_projective()),
                    )?);
                }

                let d_gadget =
                    FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc(cs.ns(|| format!("alloc_d_{}", i)), || {
                        Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(*d as u128))
                    })?;

                res.push((*d, d_gadget, gadgets));
            }
            Some(res)
        } else {
            None
        };

        Ok(Self {
            prepared_g,
            prepared_h,
            prepared_beta_h,
            prepared_degree_bounds_and_shift_powers,
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
        let obj = value_gen()?.borrow();

        let mut prepared_g = Vec::<PG::G1Gadget>::new();
        for (i, g) in obj.prepared_vk.prepared_g.iter().enumerate() {
            prepared_g.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_input(cs.ns(|| format!("g_{}", i)), || {
                Ok(g.into_projective())
            })?);
        }

        let prepared_h = PG::G2PreparedGadget::alloc_input(cs.ns(|| "h"), || Ok(&obj.prepared_vk.prepared_h))?;
        let prepared_beta_h =
            PG::G2PreparedGadget::alloc_input(cs.ns(|| "beta_h"), || Ok(&obj.prepared_vk.prepared_beta_h))?;

        let prepared_degree_bounds_and_shift_powers = if obj.prepared_degree_bounds_and_shift_powers.is_some() {
            let mut res = Vec::<(usize, FpGadget<<BaseCurve as PairingEngine>::Fr>, Vec<PG::G1Gadget>)>::new();

            for (i, (d, shift_power_elems)) in obj
                .prepared_degree_bounds_and_shift_powers
                .as_ref()
                .unwrap()
                .iter()
                .enumerate()
            {
                let mut gadgets = Vec::<PG::G1Gadget>::new();
                for (j, shift_power_elem) in shift_power_elems.iter().enumerate() {
                    gadgets.push(<PG::G1Gadget as AllocGadget<
                        <TargetCurve as PairingEngine>::G1Projective,
                        <BaseCurve as PairingEngine>::Fr,
                    >>::alloc_input(
                        cs.ns(|| format!("alloc_input_gadget_{}_{}", i, j)),
                        || Ok(shift_power_elem.into_projective()),
                    )?);
                }

                let d_gadget = FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc_input(
                    cs.ns(|| format!("alloc_input_d_{}", i)),
                    || Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(*d as u128)),
                )?;

                res.push((*d, d_gadget, gadgets));
            }
            Some(res)
        } else {
            None
        };

        Ok(Self {
            prepared_g,
            prepared_h,
            prepared_beta_h,
            prepared_degree_bounds_and_shift_powers,
            constant_allocation: true,
            origin_vk: None,
        })
    }
}

/// Var for an optionally hiding Marlin-KZG10 commitment.
pub struct CommitmentVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    comm: PG::G1Gadget,
    shifted_comm: Option<PG::G1Gadget>,
}

impl<TargetCurve, BaseCurve, PG> Clone for CommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,

    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self {
            comm: self.comm.clone(),
            shifted_comm: self.shifted_comm.clone(),
        }
    }
}

impl<TargetCurve, BaseCurve, PG> AllocGadget<Commitment<TargetCurve>, <BaseCurve as PairingEngine>::Fr>
    for CommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,

    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Commitment<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|commitment| {
            let commitment = *commitment.borrow();
            let comm = commitment.comm;
            let comm_gadget =
                PG::G1Gadget::alloc_constant(cs.ns(|| "alloc_constant_commitment"), || Ok(comm.0.into_projective()))?;

            let shifted_comm = commitment.shifted_comm;
            let shifted_comm_gadget = if let Some(shifted_comm) = shifted_comm {
                Some(PG::G1Gadget::alloc_constant(
                    cs.ns(|| "alloc_constant_shifted_commitment"),
                    || Ok(shifted_comm.0.into_projective()),
                )?)
            } else {
                None
            };

            Ok(Self {
                comm: comm_gadget,
                shifted_comm: shifted_comm_gadget,
            })
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Commitment<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|commitment| {
            let commitment = *commitment.borrow();
            let comm = commitment.comm;
            let comm_gadget = PG::G1Gadget::alloc(cs.ns(|| "alloc_commitment"), || Ok(comm.0.into_projective()))?;

            let shifted_comm = commitment.shifted_comm;
            let shifted_comm_gadget = if let Some(shifted_comm) = shifted_comm {
                Some(PG::G1Gadget::alloc(cs.ns(|| "alloc_shifted_commitment"), || {
                    Ok(shifted_comm.0.into_projective())
                })?)
            } else {
                None
            };

            Ok(Self {
                comm: comm_gadget,
                shifted_comm: shifted_comm_gadget,
            })
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Commitment<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|commitment| {
            let commitment = *commitment.borrow();
            let comm = commitment.comm;
            let comm_gadget =
                PG::G1Gadget::alloc_input(cs.ns(|| "alloc_input_commitment"), || Ok(comm.0.into_projective()))?;

            let shifted_comm = commitment.shifted_comm;
            let shifted_comm_gadget = if let Some(shifted_comm) = shifted_comm {
                Some(PG::G1Gadget::alloc_input(
                    cs.ns(|| "alloc_input_shifted_commitment"),
                    || Ok(shifted_comm.0.into_projective()),
                )?)
            } else {
                None
            };

            Ok(Self {
                comm: comm_gadget,
                shifted_comm: shifted_comm_gadget,
            })
        })
    }
}

impl<TargetCurve, BaseCurve, PG> ToConstraintFieldGadget<<BaseCurve as PairingEngine>::Fr>
    for CommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    PG::G1Gadget: ToConstraintFieldGadget<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn to_constraint_field(&self) -> Result<Vec<FpGadget<<BaseCurve as PairingEngine>::Fr>>, SynthesisError> {
        let mut res = Vec::new();

        let mut comm_gadget = self.comm.to_constraint_field()?;

        res.append(&mut comm_gadget);

        if self.shifted_comm.as_ref().is_some() {
            let mut shifted_comm_gadget = self.shifted_comm.as_ref().unwrap().to_constraint_field()?;
            res.append(&mut shifted_comm_gadget);
        }

        Ok(res)
    }
}

impl<TargetCurve, BaseCurve, PG> ToBytesGadget<<BaseCurve as PairingEngine>::Fr>
    for CommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn to_bytes<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        let zero_shifted_comm = PG::G1Gadget::zero(cs.ns(|| "zero"))?;

        let mut bytes = Vec::new();
        bytes.extend_from_slice(&self.comm.to_bytes(cs.ns(|| "comm_to_bytes"))?);

        let shifted_comm = self.shifted_comm.clone().unwrap_or(zero_shifted_comm);
        bytes.extend_from_slice(&shifted_comm.to_bytes(cs.ns(|| "shifted_comm_to_bytes"))?);
        Ok(bytes)
    }

    fn to_bytes_strict<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

/// Prepared gadget for an optionally hiding Marlin-KZG10 commitment.
/// shifted_comm is not prepared, due to the specific use case.
pub struct PreparedCommitmentVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    prepared_comm: Vec<PG::G1Gadget>,
    shifted_comm: Option<PG::G1Gadget>,
}

impl<TargetCurve, BaseCurve, PG> Clone for PreparedCommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self {
            prepared_comm: self.prepared_comm.clone(),
            shifted_comm: self.shifted_comm.clone(),
        }
    }
}

impl<TargetCurve, BaseCurve, PG>
    PrepareGadget<CommitmentVar<TargetCurve, BaseCurve, PG>, <BaseCurve as PairingEngine>::Fr>
    for PreparedCommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn prepare<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        mut cs: CS,
        unprepared: &CommitmentVar<TargetCurve, BaseCurve, PG>,
    ) -> Result<Self, SynthesisError> {
        let mut prepared_comm = Vec::<PG::G1Gadget>::new();
        let supported_bits = <<TargetCurve as PairingEngine>::Fr as PrimeField>::size_in_bits();

        let mut cur: PG::G1Gadget = unprepared.comm.clone();
        for i in 0..supported_bits {
            prepared_comm.push(cur.clone());
            cur.double_in_place(cs.ns(|| format!("cur_double_in_place_{}", i)))?;
        }

        Ok(Self {
            prepared_comm,
            shifted_comm: unprepared.shifted_comm.clone(),
        })
    }
}

impl<TargetCurve, BaseCurve, PG> AllocGadget<PreparedCommitment<TargetCurve>, <BaseCurve as PairingEngine>::Fr>
    for PreparedCommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedCommitment<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?.borrow();

        let mut prepared_comm = Vec::<PG::G1Gadget>::new();

        for (i, comm_elem) in obj.prepared_comm.0.iter().enumerate() {
            prepared_comm.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_constant(
                cs.ns(|| format!("comm_elem_{}", i)),
                || {
                    Ok(<<TargetCurve as PairingEngine>::G1Projective as From<
                        <TargetCurve as PairingEngine>::G1Affine,
                    >>::from(*comm_elem))
                },
            )?);
        }

        let shifted_comm = if obj.shifted_comm.is_some() {
            Some(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_constant(cs.ns(|| "shifted_comm"), || {
                Ok(<<TargetCurve as PairingEngine>::G1Projective as From<
                    <TargetCurve as PairingEngine>::G1Affine,
                >>::from(obj.shifted_comm.unwrap().0))
            })?)
        } else {
            None
        };

        Ok(Self {
            prepared_comm,
            shifted_comm,
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedCommitment<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?.borrow();

        let mut prepared_comm = Vec::<PG::G1Gadget>::new();

        for (i, comm_elem) in obj.prepared_comm.0.iter().enumerate() {
            prepared_comm.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc(cs.ns(|| format!("comm_elem_{}", i)), || {
                Ok(<<TargetCurve as PairingEngine>::G1Projective as From<
                    <TargetCurve as PairingEngine>::G1Affine,
                >>::from(*comm_elem))
            })?);
        }

        let shifted_comm = if obj.shifted_comm.is_some() {
            Some(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc(cs.ns(|| "shifted_comm"), || {
                Ok(<<TargetCurve as PairingEngine>::G1Projective as From<
                    <TargetCurve as PairingEngine>::G1Affine,
                >>::from(obj.shifted_comm.unwrap().0))
            })?)
        } else {
            None
        };

        Ok(Self {
            prepared_comm,
            shifted_comm,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedCommitment<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let obj = value_gen()?.borrow();

        let mut prepared_comm = Vec::<PG::G1Gadget>::new();

        for (i, comm_elem) in obj.prepared_comm.0.iter().enumerate() {
            prepared_comm.push(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_input(
                cs.ns(|| format!("comm_elem_{}", i)),
                || {
                    Ok(<<TargetCurve as PairingEngine>::G1Projective as From<
                        <TargetCurve as PairingEngine>::G1Affine,
                    >>::from(*comm_elem))
                },
            )?);
        }

        let shifted_comm = if obj.shifted_comm.is_some() {
            Some(<PG::G1Gadget as AllocGadget<
                <TargetCurve as PairingEngine>::G1Projective,
                <BaseCurve as PairingEngine>::Fr,
            >>::alloc_input(cs.ns(|| "shifted_comm"), || {
                Ok(<<TargetCurve as PairingEngine>::G1Projective as From<
                    <TargetCurve as PairingEngine>::G1Affine,
                >>::from(obj.shifted_comm.unwrap().0))
            })?)
        } else {
            None
        };

        Ok(Self {
            prepared_comm,
            shifted_comm,
        })
    }
}

/// Var for a Marlin-KZG10 commitment, with a string label and degree bound.
pub struct LabeledCommitmentVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    /// A text label for the commitment.
    pub label: String,
    /// The plain commitment.
    pub commitment: CommitmentVar<TargetCurve, BaseCurve, PG>,
    /// Optionally, a bound on the polynomial degree.
    pub degree_bound: Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
}

impl<TargetCurve, BaseCurve, PG> Clone for LabeledCommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        LabeledCommitmentVar {
            label: self.label.clone(),
            commitment: self.commitment.clone(),
            degree_bound: self.degree_bound.clone(),
        }
    }
}

impl<TargetCurve, BaseCurve, PG>
    AllocGadget<LabeledCommitment<Commitment<TargetCurve>>, <BaseCurve as PairingEngine>::Fr>
    for LabeledCommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<LabeledCommitment<Commitment<TargetCurve>>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|labeled_commitment| {
            let labeled_commitment = labeled_commitment.borrow().clone();
            let label = labeled_commitment.label().to_string();
            let commitment = labeled_commitment.commitment();
            let degree_bound = labeled_commitment.degree_bound();

            let commitment = CommitmentVar::alloc_constant(cs.ns(|| "commitment"), || Ok(commitment))?;

            let degree_bound = if let Some(degree_bound) = degree_bound {
                FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc_constant(cs.ns(|| "degree_bound"), || {
                    Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(
                        degree_bound as u128,
                    ))
                })
                .ok()
            } else {
                None
            };

            Ok(Self {
                label,
                commitment,
                degree_bound,
            })
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<LabeledCommitment<Commitment<TargetCurve>>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|labeled_commitment| {
            let labeled_commitment = labeled_commitment.borrow().clone();
            let label = labeled_commitment.label().to_string();
            let commitment = labeled_commitment.commitment();
            let degree_bound = labeled_commitment.degree_bound();

            let commitment = CommitmentVar::alloc(cs.ns(|| "commitment"), || Ok(commitment))?;

            let degree_bound = if let Some(degree_bound) = degree_bound {
                FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc(cs.ns(|| "degree_bound"), || {
                    Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(
                        degree_bound as u128,
                    ))
                })
                .ok()
            } else {
                None
            };

            Ok(Self {
                label,
                commitment,
                degree_bound,
            })
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<LabeledCommitment<Commitment<TargetCurve>>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|labeled_commitment| {
            let labeled_commitment = labeled_commitment.borrow().clone();
            let label = labeled_commitment.label().to_string();
            let commitment = labeled_commitment.commitment();
            let degree_bound = labeled_commitment.degree_bound();

            let commitment = CommitmentVar::alloc_input(cs.ns(|| "commitment"), || Ok(commitment))?;

            let degree_bound = if let Some(degree_bound) = degree_bound {
                FpGadget::<<BaseCurve as PairingEngine>::Fr>::alloc_input(cs.ns(|| "degree_bound"), || {
                    Ok(<<BaseCurve as PairingEngine>::Fr as From<u128>>::from(
                        degree_bound as u128,
                    ))
                })
                .ok()
            } else {
                None
            };

            Ok(Self {
                label,
                commitment,
                degree_bound,
            })
        })
    }
}

/// Var for a Marlin-KZG10 commitment, with a string label and degree bound.
pub struct PreparedLabeledCommitmentVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    /// A text label for the commitment.
    pub label: String,
    /// The plain commitment.
    pub prepared_commitment: PreparedCommitmentVar<TargetCurve, BaseCurve, PG>,
    /// Optionally, a bound on the polynomial degree.
    pub degree_bound: Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
}

impl<TargetCurve, BaseCurve, PG> Clone for PreparedLabeledCommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self {
            label: self.label.clone(),
            prepared_commitment: self.prepared_commitment.clone(),
            degree_bound: self.degree_bound.clone(),
        }
    }
}

impl<TargetCurve, BaseCurve, PG>
    PrepareGadget<LabeledCommitmentVar<TargetCurve, BaseCurve, PG>, <BaseCurve as PairingEngine>::Fr>
    for PreparedLabeledCommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn prepare<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        cs: CS,
        unprepared: &LabeledCommitmentVar<TargetCurve, BaseCurve, PG>,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            label: unprepared.label.clone(),
            prepared_commitment: PreparedCommitmentVar::prepare(cs, &unprepared.commitment)?,
            degree_bound: unprepared.degree_bound.clone(),
        })
    }
}

/// Var for a Marlin-KZG10 proof.
#[allow(clippy::type_complexity)]
pub struct ProofVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    /// The commitment to the witness polynomial.
    pub w: PG::G1Gadget,
    /// The evaluation of the random hiding polynomial.
    pub random_v: Option<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
}

impl<TargetCurve, BaseCurve, PG> Clone for ProofVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self {
            w: self.w.clone(),
            random_v: self.random_v.clone(),
        }
    }
}

impl<TargetCurve, BaseCurve, PG> AllocGadget<Proof<TargetCurve>, <BaseCurve as PairingEngine>::Fr>
    for ProofVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|proof| {
            let Proof { w, random_v } = *proof.borrow();
            let w = PG::G1Gadget::alloc_constant(cs.ns(|| "alloc_constant_w"), || Ok(w.into_projective()))?;

            let random_v = match random_v {
                None => None,
                Some(random_v_inner) => Some(NonNativeFieldVar::alloc_constant(
                    cs.ns(|| "alloc_constant_random_v"),
                    || Ok(random_v_inner),
                )?),
            };

            Ok(Self { w, random_v })
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|proof| {
            let Proof { w, random_v } = *proof.borrow();
            let w = PG::G1Gadget::alloc(cs.ns(|| "alloc_w"), || Ok(w.into_projective()))?;

            let random_v = match random_v {
                None => None,
                Some(random_v_inner) => Some(NonNativeFieldVar::alloc(cs.ns(|| "alloc_random_v"), || {
                    Ok(random_v_inner)
                })?),
            };

            Ok(Self { w, random_v })
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|proof| {
            let Proof { w, random_v } = *proof.borrow();
            let w = PG::G1Gadget::alloc_input(cs.ns(|| "alloc_input_w"), || Ok(w.into_projective()))?;

            let random_v = match random_v {
                None => None,
                Some(random_v_inner) => Some(NonNativeFieldVar::alloc_input(
                    cs.ns(|| "alloc_input_random_v"),
                    || Ok(random_v_inner),
                )?),
            };

            Ok(Self { w, random_v })
        })
    }
}

/// An allocated version of `BatchLCProof`.
#[allow(clippy::type_complexity)]
pub struct BatchLCProofVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    /// Evaluation proofs.
    pub proofs: Vec<ProofVar<TargetCurve, BaseCurve, PG>>,
    /// Evaluations required to verify the proof.
    pub evals: Option<Vec<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>>,
}

impl<TargetCurve, BaseCurve, PG> Clone for BatchLCProofVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self {
            proofs: self.proofs.clone(),
            evals: self.evals.clone(),
        }
    }
}

impl<TargetCurve, BaseCurve, PG>
    AllocGadget<
        BatchLCProof<<TargetCurve as PairingEngine>::Fr, MarlinKZG10<TargetCurve>>,
        <BaseCurve as PairingEngine>::Fr,
    > for BatchLCProofVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BatchLCProof<<TargetCurve as PairingEngine>::Fr, MarlinKZG10<TargetCurve>>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().map(|proof| {
            let BatchLCProof { proof, evaluations } = proof.borrow().clone();

            let proofs: Vec<Proof<_>> = proof.to_vec();
            let proofs: Vec<ProofVar<TargetCurve, BaseCurve, PG>> = proofs
                .iter()
                .map(|p| ProofVar::alloc_constant(cs.ns(|| "proof"), || Ok(p)).unwrap())
                .collect();

            #[allow(clippy::type_complexity)]
            let evals: Option<
                Vec<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
            > = match evaluations {
                None => None,
                Some(evals_inner) => Some(
                    evals_inner
                        .iter()
                        .map(|e| NonNativeFieldVar::alloc_constant(cs.ns(|| "evaluation"), || Ok(e)).unwrap())
                        .collect(),
                ),
            };

            Self { proofs, evals }
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BatchLCProof<<TargetCurve as PairingEngine>::Fr, MarlinKZG10<TargetCurve>>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().map(|proof| {
            let BatchLCProof { proof, evaluations } = proof.borrow().clone();

            let proofs: Vec<Proof<_>> = proof.to_vec();
            let proofs: Vec<ProofVar<TargetCurve, BaseCurve, PG>> = proofs
                .iter()
                .map(|p| ProofVar::alloc(cs.ns(|| "proof"), || Ok(p)).unwrap())
                .collect();

            #[allow(clippy::type_complexity)]
            let evals: Option<
                Vec<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
            > = match evaluations {
                None => None,
                Some(evals_inner) => Some(
                    evals_inner
                        .iter()
                        .map(|e| NonNativeFieldVar::alloc(cs.ns(|| "evaluation"), || Ok(e)).unwrap())
                        .collect(),
                ),
            };

            Self { proofs, evals }
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<BatchLCProof<<TargetCurve as PairingEngine>::Fr, MarlinKZG10<TargetCurve>>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().map(|proof| {
            let BatchLCProof { proof, evaluations } = proof.borrow().clone();

            let proofs: Vec<Proof<_>> = proof.to_vec();
            let proofs: Vec<ProofVar<TargetCurve, BaseCurve, PG>> = proofs
                .iter()
                .map(|p| ProofVar::alloc_input(cs.ns(|| "proof"), || Ok(p)).unwrap())
                .collect();

            #[allow(clippy::type_complexity)]
            let evals: Option<
                Vec<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
            > = match evaluations {
                None => None,
                Some(evals_inner) => Some(
                    evals_inner
                        .iter()
                        .map(|e| NonNativeFieldVar::alloc_input(cs.ns(|| "evaluation"), || Ok(e)).unwrap())
                        .collect(),
                ),
            };

            Self { proofs, evals }
        })
    }
}

/// Var for the Marlin-KZG10 polynomial commitment verifier.
pub struct MarlinKZG10Gadget<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    _target_curve: PhantomData<TargetCurve>,
    _base_curve: PhantomData<BaseCurve>,
    _pairing_gadget: PhantomData<PG>,
}

impl<TargetCurve, BaseCurve, PG> Clone for MarlinKZG10Gadget<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self {
            _target_curve: PhantomData,
            _base_curve: PhantomData,
            _pairing_gadget: PhantomData,
        }
    }
}

impl<TargetCurve, BaseCurve, PG> MarlinKZG10Gadget<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn prepared_batch_check_evaluations<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        mut cs: CS,
        prepared_verification_key: &<Self as PCCheckVar<
            <TargetCurve as PairingEngine>::Fr,
            MarlinKZG10<TargetCurve>,
            <BaseCurve as PairingEngine>::Fr,
        >>::PreparedVerifierKeyVar,
        lc_info: &[(
            String,
            Vec<(
                Option<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
                Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
                PreparedCommitmentVar<TargetCurve, BaseCurve, PG>,
                bool,
            )>,
        )],
        query_set: &QuerySetVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
        evaluations: &EvaluationsVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
        proofs: &[<Self as PCCheckVar<
            <TargetCurve as PairingEngine>::Fr,
            MarlinKZG10<TargetCurve>,
            <BaseCurve as PairingEngine>::Fr,
        >>::ProofVar],
        opening_challenges: &[NonNativeFieldVar<
            <TargetCurve as PairingEngine>::Fr,
            <BaseCurve as PairingEngine>::Fr,
        >],
        opening_challenges_bits: &[Vec<Boolean>],
        batching_rands: &[NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>],
        batching_rands_bits: &[Vec<Boolean>],
    ) -> Result<Boolean, SynthesisError> {
        let mut batching_rands = batching_rands.to_vec();
        let mut batching_rands_bits = batching_rands_bits.to_vec();

        let commitment_lcs: BTreeMap<
            String,
            (
                String,
                Vec<(
                    Option<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
                    Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
                    PreparedCommitmentVar<TargetCurve, BaseCurve, PG>,
                    bool,
                )>,
            ),
        > = lc_info.iter().map(|c| (c.0.clone(), c.clone())).collect();

        let mut query_to_labels_map = BTreeMap::new();

        for (label, point) in query_set.0.iter() {
            let labels = query_to_labels_map
                .entry(point.name.clone())
                .or_insert((point.value.clone(), BTreeSet::new()));
            labels.1.insert(label);
        }

        println!("before PC combining commitments: constraints: {}", cs.num_constraints());

        // Accumulate commitments and evaluations for each query.
        let mut combined_queries = Vec::new();
        let mut combined_comms = Vec::new();
        let mut combined_evals = Vec::new();
        for (i, (_, (point, labels))) in query_to_labels_map.into_iter().enumerate() {
            let mut comms_to_combine = Vec::<
                Vec<(
                    Option<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
                    Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
                    PreparedCommitmentVar<TargetCurve, BaseCurve, PG>,
                    bool,
                )>,
            >::new();
            let mut values_to_combine = Vec::new();
            for label in labels.into_iter() {
                let commitment_lc = commitment_lcs.get(label).unwrap().clone();

                let v_i = evaluations
                    .0
                    .get(&LabeledPointVar {
                        name: label.clone(),
                        value: point.clone(),
                    })
                    .unwrap();

                comms_to_combine.push(commitment_lc.1.clone());
                values_to_combine.push(v_i.clone());
            }

            // Accumulate the commitments and evaluations corresponding to `query`.
            let mut combined_comm = PG::G1Gadget::zero(cs.ns(|| "comm_zero"))?;
            let mut combined_eval = NonNativeFieldMulResultVar::<
                <TargetCurve as PairingEngine>::Fr,
                <BaseCurve as PairingEngine>::Fr,
            >::zero();

            let mut opening_challenges_counter = 0;

            for (j, (commitment_lcs, value)) in comms_to_combine.into_iter().zip(values_to_combine).enumerate() {
                let challenge = opening_challenges[opening_challenges_counter].clone();

                let challenge_bits = opening_challenges_bits[opening_challenges_counter].clone();
                opening_challenges_counter += 1;

                for (k, (coeff, degree_bound, comm, negate)) in commitment_lcs.iter().enumerate() {
                    let PreparedCommitmentVar { shifted_comm, .. } = comm;

                    if coeff.is_none() {
                        // To combine the commitments, we multiply each by one of the random challenges, and sum.
                        let mut comm_times_challenge = PG::G1Gadget::zero(cs.ns(|| format!("zero_{}_{}_{}", i, j, k)))?;
                        {
                            for (bit, base_power) in challenge_bits.iter().zip(comm.prepared_comm.iter()) {
                                let mut new_encoded = base_power.clone();
                                new_encoded = new_encoded.add(
                                    cs.ns(|| format!("new_encoded_plus_comm_times_challenge_{}_{}_{}", i, j, k)),
                                    &comm_times_challenge,
                                )?;
                                comm_times_challenge = PG::G1Gadget::conditionally_select(
                                    cs.ns(|| format!("comm_times_challenge_cond_select_{}_{}_{}", i, j, k)),
                                    bit,
                                    &new_encoded,
                                    &comm_times_challenge,
                                )?;
                            }
                        }

                        if negate.eq(&true) {
                            comm_times_challenge = comm_times_challenge
                                .negate(cs.ns(|| format!("negate_comm_times_challenge_{}_{}_{}", i, j, k)))?;
                        }

                        combined_comm = combined_comm.add(
                            cs.ns(|| format!("combined_comm_plus_comm_times_challenge_{}_{}_{}", i, j, k)),
                            &comm_times_challenge,
                        )?;

                        // If the degree bound is specified, we include the adjusted degree-shifted commitment
                        // (that is, c_i' - v_i beta^{D - d_i} G), where d_i is the specific degree bound and
                        // v_i is the evaluation, in the combined commitment,
                        if let Some(degree_bound) = degree_bound {
                            let challenge_shifted_bits = opening_challenges_bits[opening_challenges_counter].clone();
                            opening_challenges_counter += 1;

                            let mut shifted_comm = shifted_comm.clone().unwrap();

                            if negate.eq(&true) {
                                shifted_comm =
                                    shifted_comm.negate(cs.ns(|| format!("shifted_comm_negate_{}_{}_{}", i, j, k)))?;
                            }

                            let value_bits =
                                value.to_bits_le(cs.ns(|| format!("value_to_bits_le_{}_{}_{}", i, j, k)))?;
                            let shift_power = prepared_verification_key
                                .get_shift_power(
                                    cs.ns(|| format!("prepared_vk_get_shift_power_{}_{}_{}", i, j, k)),
                                    degree_bound,
                                )
                                .unwrap();

                            let mut shift_power_times_value =
                                PG::G1Gadget::zero(cs.ns(|| format!("shift_power_times_value_zero{}_{}_{}", i, j, k)))?;
                            {
                                for (l, (bit, base_power)) in value_bits.iter().zip(&shift_power).enumerate() {
                                    let mut new_encoded = base_power.clone();
                                    new_encoded = new_encoded.add(
                                        cs.ns(|| {
                                            format!("new_encoded_add_shift_power_times_value_{}_{}_{}_{}", i, j, k, l)
                                        }),
                                        &shift_power_times_value,
                                    )?;

                                    shift_power_times_value = PG::G1Gadget::conditionally_select(
                                        cs.ns(|| format!("shift_power_times_value_cond_select{}_{}_{}_{}", i, j, k, l)),
                                        bit,
                                        &new_encoded,
                                        &shift_power_times_value,
                                    )?;
                                }
                            }
                            let mut adjusted_comm = shifted_comm;
                            adjusted_comm = adjusted_comm.sub(
                                cs.ns(|| format!("adjusted_comm_minus_shift_power_times_value_{}_{}_{}", i, j, k)),
                                &shift_power_times_value,
                            )?;

                            let adjusted_comm_times_challenge =
                                adjusted_comm.scalar_mul_le(challenge_shifted_bits.iter())?;
                            combined_comm = combined_comm.add(
                                cs.ns(|| format!("combined_comm_add_adjusted_comm_times_challenge_{}_{}_{}", i, j, k)),
                                &adjusted_comm_times_challenge,
                            )?;
                        }
                    } else {
                        assert!(degree_bound.is_none());

                        let mut comm_times_challenge = PG::G1Gadget::zero(cs.ns(|| format!("zero_{}_{}_{}", i, j, k)))?;
                        let coeff = coeff.clone().unwrap();

                        let challenge_times_coeff = challenge.mul(
                            &mut cs.ns(|| format!("challenge_times_coeff_{}_{}_{}", i, j, k)),
                            &coeff,
                        )?;

                        let challenge_times_coeff_bits = challenge_times_coeff
                            .to_bits_le(cs.ns(|| format!("challenge_times_coeff_to_bits_le_{}_{}_{}", i, j, k)))?;

                        {
                            for (bit, base_power) in challenge_times_coeff_bits.iter().zip(&comm.prepared_comm) {
                                let mut new_encoded = comm_times_challenge.clone();
                                new_encoded = new_encoded.add(
                                    cs.ns(|| format!("new_encoded_add_base_power_{}_{}_{}", i, j, k)),
                                    &base_power,
                                )?;

                                comm_times_challenge = PG::G1Gadget::conditionally_select(
                                    cs.ns(|| format!("comm_times_challenge_cond_select_{}_{}_{}", i, j, k)),
                                    bit,
                                    &new_encoded,
                                    &comm_times_challenge,
                                )?;
                            }
                        }

                        if negate.eq(&true) {
                            comm_times_challenge = comm_times_challenge
                                .negate(cs.ns(|| format!("comm_times_challenge_negate_{}_{}_{}", i, j, k)))?;
                        }

                        combined_comm = combined_comm.add(
                            &mut cs.ns(|| format!("combined_comm_add_comm_times_challenge_{}_{}_{}", i, j, k)),
                            &comm_times_challenge,
                        )?;
                    }
                }
                // Similarly, we add up the evaluations, multiplied with random challenges.
                let value_times_challenge_unreduced =
                    value.mul_without_reduce(cs.ns(|| format!("value_mul_without_reduce_{}_{}", i, j)), &challenge)?;

                combined_eval = combined_eval.add(
                    &mut cs.ns(|| format!("combined_eval_add_value_times_challenge_unreduced_{}_{}", i, j)),
                    &value_times_challenge_unreduced,
                )?;
            }

            let combined_eval_reduced = combined_eval.reduce(&mut cs.ns(|| format!("combined_eval_reduced_{}", i)))?;

            combined_queries.push(point.clone());
            combined_comms.push(combined_comm);
            combined_evals.push(combined_eval_reduced);
        }

        println!("before PC batch check: constraints: {}", cs.num_constraints());

        // Perform the batch check.
        {
            let mut total_c = PG::G1Gadget::zero(cs.ns(|| "zero_c"))?;
            let mut total_w = PG::G1Gadget::zero(cs.ns(|| "zero_w"))?;

            let mut g_multiplier = NonNativeFieldMulResultVar::<
                <TargetCurve as PairingEngine>::Fr,
                <BaseCurve as PairingEngine>::Fr,
            >::zero();
            let mut g_multiplier_reduced = NonNativeFieldVar::<
                <TargetCurve as PairingEngine>::Fr,
                <BaseCurve as PairingEngine>::Fr,
            >::zero(cs.ns(|| "zero_g_multiplier"))?;
            for (i, (((c, z), v), proof)) in combined_comms
                .iter()
                .zip(combined_queries)
                .zip(combined_evals)
                .zip(proofs)
                .enumerate()
            {
                let z_bits = z.to_bits_le(cs.ns(|| format!("z_bits_to_le_{}", i)))?;

                let w_times_z = proof.w.scalar_mul_le(z_bits.iter())?;

                let mut c_plus_w_times_z = c.clone();
                c_plus_w_times_z =
                    c_plus_w_times_z.add(cs.ns(|| format!("c_plus_w_times_z_plus_w_times_z_{}", i)), w_times_z)?;

                if i != 0 {
                    let randomizer = batching_rands.remove(0);
                    let randomizer_bits = batching_rands_bits.remove(0);

                    let randomizer_times_v =
                        randomizer.mul_without_reduce(cs.ns(|| format!("mul_without_reduce_{}", i)), &v)?;

                    g_multiplier = g_multiplier.add(
                        &mut cs.ns(|| format!("g_multiplier_plus_randomizer_times_v_{}", i)),
                        &randomizer_times_v,
                    )?;

                    let c_times_randomizer = c_plus_w_times_z.scalar_mul_le(randomizer_bits.iter())?;
                    let w_times_randomizer = proof.w.scalar_mul_le(randomizer_bits.iter())?;
                    total_c = total_c.add(
                        &mut cs.ns(|| format!("total_c_plus_c_times_randomizer_{}", i)),
                        &c_times_randomizer,
                    )?;
                    total_w = total_w.add(
                        &mut cs.ns(|| format!("total_w_plus_w_times_randomizer_{}", i)),
                        &w_times_randomizer,
                    )?;
                } else {
                    g_multiplier_reduced =
                        g_multiplier_reduced.add(&mut cs.ns(|| format!("g_multiplier_reduced_plus_v_{}", i)), &v)?;
                    total_c = total_c.add(
                        &mut cs.ns(|| format!("total_c_plus_c_plus_w_times_z_{}", i)),
                        &c_plus_w_times_z,
                    )?;
                    total_w = total_w.add(&mut cs.ns(|| format!("total_w_plus_proof_w{}", i)), &proof.w)?;
                }
            }

            // Prepare each input to the pairing.
            let (prepared_total_w, prepared_beta_h, prepared_total_c, prepared_h) = {
                let g_multiplier_reduced = g_multiplier_reduced.add(
                    &mut cs.ns(|| "g_multiplier_reduce"),
                    &g_multiplier.reduce(&mut cs.ns(|| "g_multiplier_reduce_sum"))?,
                )?;
                let g_multiplier_bits = g_multiplier_reduced.to_bits_le(&mut cs.ns(|| "g_multiplier_to_bits_le"))?;

                let mut g_times_mul = PG::G1Gadget::zero(cs.ns(|| "g_times_mul_zero"))?;
                {
                    for (i, (bit, base_power)) in g_multiplier_bits
                        .iter()
                        .zip(&prepared_verification_key.prepared_g)
                        .enumerate()
                    {
                        let mut new_encoded = g_times_mul.clone();
                        new_encoded =
                            new_encoded.add(cs.ns(|| format!("new_encoded_plus_base_power_{}", i)), base_power)?;

                        g_times_mul = PG::G1Gadget::conditionally_select(
                            cs.ns(|| format!("g_times_mul_cond_select_{}", i)),
                            bit,
                            &new_encoded,
                            &g_times_mul,
                        )?;
                    }
                }

                total_c = total_c.sub(&mut cs.ns(|| "total_c_minus_g_times_mul"), &g_times_mul)?;
                total_w = total_w.negate(cs.ns(|| "total_w_negate"))?;

                let prepared_total_w = PG::prepare_g1(cs.ns(|| "prepared_total_w"), total_w)?;
                let prepared_beta_h = prepared_verification_key.prepared_beta_h.clone();
                let prepared_total_c = PG::prepare_g1(cs.ns(|| "prepared_total_c"), total_c)?;
                let prepared_h = prepared_verification_key.prepared_h.clone();

                (prepared_total_w, prepared_beta_h, prepared_total_c, prepared_h)
            };

            let lhs = PG::product_of_pairings(
                cs.ns(|| "lhs_product_of_pairings"),
                &[prepared_total_w, prepared_total_c],
                &[prepared_beta_h, prepared_h],
            )?;

            println!("after PC batch check: constraints: {}", cs.num_constraints());

            let rhs = &PG::GTGadget::one(cs.ns(|| "rhs"))?;
            lhs.is_eq(&rhs)
        }
    }
}

impl<TargetCurve, BaseCurve, PG>
    PCCheckVar<<TargetCurve as PairingEngine>::Fr, MarlinKZG10<TargetCurve>, <BaseCurve as PairingEngine>::Fr>
    for MarlinKZG10Gadget<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G1Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G2Projective: MulAssign<<BaseCurve as PairingEngine>::Fq>,
    <TargetCurve as PairingEngine>::G1Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
    <TargetCurve as PairingEngine>::G2Affine: ToConstraintField<<BaseCurve as PairingEngine>::Fr>,
{
    type BatchLCProofVar = BatchLCProofVar<TargetCurve, BaseCurve, PG>;
    type CommitmentVar = CommitmentVar<TargetCurve, BaseCurve, PG>;
    type LabeledCommitmentVar = LabeledCommitmentVar<TargetCurve, BaseCurve, PG>;
    type PreparedCommitmentVar = PreparedCommitmentVar<TargetCurve, BaseCurve, PG>;
    type PreparedLabeledCommitmentVar = PreparedLabeledCommitmentVar<TargetCurve, BaseCurve, PG>;
    type PreparedVerifierKeyVar = PreparedVerifierKeyVar<TargetCurve, BaseCurve, PG>;
    type ProofVar = ProofVar<TargetCurve, BaseCurve, PG>;
    type VerifierKeyVar = VerifierKeyVar<TargetCurve, BaseCurve, PG>;

    #[allow(clippy::type_complexity)]
    fn batch_check_evaluations<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        mut cs: CS,
        verification_key: &Self::VerifierKeyVar,
        commitments: &[Self::LabeledCommitmentVar],
        query_set: &QuerySetVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
        evaluations: &EvaluationsVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
        proofs: &[Self::ProofVar],
        rand_data: &PCCheckRandomDataVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
    ) -> Result<Boolean, SynthesisError> {
        let mut batching_rands = rand_data.batching_rands.to_vec();
        let mut batching_rands_bits = rand_data.batching_rands_bits.to_vec();

        let commitments: BTreeMap<_, _> = commitments.iter().map(|c| (c.label.clone(), c)).collect();
        let mut query_to_labels_map = BTreeMap::new();

        for (label, point) in query_set.0.iter() {
            let labels = query_to_labels_map
                .entry(point.name.clone())
                .or_insert((point.value.clone(), BTreeSet::new()));
            labels.1.insert(label);
        }

        // Accumulate commitments and evaluations for each query.
        let mut combined_queries = Vec::new();
        let mut combined_comms = Vec::new();
        let mut combined_evals = Vec::new();
        for (_, (point, labels)) in query_to_labels_map.into_iter() {
            let mut comms_to_combine: Vec<Self::LabeledCommitmentVar> = Vec::new();
            let mut values_to_combine = Vec::new();
            for label in labels.into_iter() {
                let commitment = &(*commitments.get(label).unwrap()).clone();
                let degree_bound = commitment.degree_bound.clone();
                assert_eq!(degree_bound.is_some(), commitment.commitment.shifted_comm.is_some());

                let v_i = evaluations
                    .0
                    .get(&LabeledPointVar {
                        name: label.clone(),
                        value: point.clone(),
                    })
                    .unwrap();

                comms_to_combine.push(commitment.clone());
                values_to_combine.push(v_i.clone());
            }

            // Accumulate the commitments and evaluations corresponding to `query`.
            let mut combined_comm = PG::G1Gadget::zero(cs.ns(|| "comm_zero"))?;
            let mut combined_eval = NonNativeFieldMulResultVar::<
                <TargetCurve as PairingEngine>::Fr,
                <BaseCurve as PairingEngine>::Fr,
            >::zero();

            let mut opening_challenges_counter = 0;

            for (i, (labeled_commitment, value)) in
                comms_to_combine.into_iter().zip(values_to_combine.iter()).enumerate()
            {
                let challenge = rand_data.opening_challenges[opening_challenges_counter].clone();
                let challenge_bits = rand_data.opening_challenges_bits[opening_challenges_counter].clone();
                opening_challenges_counter += 1;

                let LabeledCommitmentVar {
                    commitment,
                    degree_bound,
                    ..
                } = labeled_commitment;
                let CommitmentVar { shifted_comm, .. } = commitment;

                // To combine the commitments, we multiply each by one of the random challenges, and sum.
                let temp = commitment.comm.scalar_mul_le(challenge_bits.iter())?;
                combined_comm =
                    combined_comm.add(cs.ns(|| format!("combined_comm_plus_scalar_product_{}", i)), &temp)?;

                // Similarly, we add up the evaluations, multiplied with random challenges.
                let value_times_challenge_unreduced =
                    value.mul_without_reduce(cs.ns(|| format!("value_mul_without_reduce_{}", i)), &challenge)?;

                combined_eval = combined_eval.add(
                    &mut cs.ns(|| format!("combined_eval_add_value_times_challenge_unreduced_{}", i)),
                    &value_times_challenge_unreduced,
                )?;

                // If the degree bound is specified, we include the adjusted degree-shifted commitment
                // (that is, c_i' - v_i beta^{D - d_i} G), where d_i is the specific degree bound and
                // v_i is the evaluation, in the cocmbined commitment,
                if let Some(degree_bound) = degree_bound {
                    let challenge_shifted_bits = rand_data.opening_challenges_bits[opening_challenges_counter].clone();
                    opening_challenges_counter += 1;

                    let shifted_comm = shifted_comm.as_ref().unwrap().clone();

                    let value_bits = value.to_bits_le(cs.ns(|| format!("value_to_bits_le_{}", i)))?;
                    let shift_power = verification_key
                        .get_shift_power(cs.ns(|| format!("get_shift_key_{}", i)), &degree_bound)
                        .unwrap();

                    let shift_power_times_value = shift_power.scalar_mul_le(value_bits.iter())?;
                    let mut adjusted_comm = shifted_comm;
                    adjusted_comm = adjusted_comm.sub(
                        &mut cs.ns(|| format!("adjusted_comm_minus_shift_power_times_value_{}", i)),
                        &shift_power_times_value,
                    )?;

                    let adjusted_comm_times_challenge = adjusted_comm.scalar_mul_le(challenge_shifted_bits.iter())?;
                    combined_comm = combined_comm.add(
                        &mut cs.ns(|| format!("combined_comm_plus_adjusted_comm_times_challenge_{}", i)),
                        &adjusted_comm_times_challenge,
                    )?;
                }
            }

            combined_queries.push(point.clone());
            combined_comms.push(combined_comm);
            combined_evals.push(combined_eval);
        }

        // Perform the batch check.
        {
            let mut total_c = PG::G1Gadget::zero(cs.ns(|| "zero_c"))?;
            let mut total_w = PG::G1Gadget::zero(cs.ns(|| "zero_w"))?;

            let mut g_multiplier = NonNativeFieldMulResultVar::<
                <TargetCurve as PairingEngine>::Fr,
                <BaseCurve as PairingEngine>::Fr,
            >::zero();
            for (i, (((c, z), v), proof)) in combined_comms
                .iter()
                .zip(combined_queries)
                .zip(combined_evals)
                .zip(proofs)
                .enumerate()
            {
                let z_bits = z.to_bits_le(cs.ns(|| format!("z_to_bits_le_{}", i)))?;

                let w_times_z = proof.w.scalar_mul_le(z_bits.iter())?;
                let mut c_plus_w_times_z = c.clone();
                c_plus_w_times_z = c_plus_w_times_z.add(
                    &mut cs.ns(|| format!("c_plus_w_times_z_plus_c_plus_w_times_z_{}", i)),
                    &w_times_z,
                )?;

                let randomizer = batching_rands.remove(0);
                let randomizer_bits = batching_rands_bits.remove(0);

                let v_reduced = v.reduce(&mut cs.ns(|| format!("v_reduce_{}", i)))?;
                let randomizer_times_v =
                    randomizer.mul_without_reduce(cs.ns(|| format!("randomizer_times_v_{}", i)), &v_reduced)?;

                g_multiplier = g_multiplier.add(
                    &mut cs.ns(|| format!("g_multiplier_plus_randomizer_times_v_{}", i)),
                    &randomizer_times_v,
                )?;

                let c_times_randomizer = c_plus_w_times_z.scalar_mul_le(randomizer_bits.iter())?;
                let w_times_randomizer = proof.w.scalar_mul_le(randomizer_bits.iter())?;
                total_c = total_c.add(
                    &mut cs.ns(|| format!("total_c_plus_c_times_randomizer_{}", i)),
                    &c_times_randomizer,
                )?;
                total_w = total_w.add(
                    &mut cs.ns(|| format!("total_w_plus_w_times_randomizer_{}", i)),
                    &w_times_randomizer,
                )?;
            }

            // Prepare each input to the pairing.
            let (prepared_total_w, prepared_beta_h, prepared_total_c, prepared_h) = {
                let g_multiplier_reduced = g_multiplier.reduce(&mut cs.ns(|| "g_multiplier_reduced"))?;
                let g_multiplier_bits = g_multiplier_reduced.to_bits_le(cs.ns(|| "g_multiplier_reduced_to_bits_le"))?;

                let g_times_mul = verification_key.g.scalar_mul_le(g_multiplier_bits.iter())?;
                total_c = total_c.sub(&mut cs.ns(|| "total_c_minus_g_times_mul"), &g_times_mul)?;
                total_w = total_w.negate(cs.ns(|| "total_w_negate"))?;

                let prepared_total_w = PG::prepare_g1(cs.ns(|| "prepared_total_w"), total_w)?;
                let prepared_beta_h = PG::prepare_g2(cs.ns(|| "prepared_beta_h"), verification_key.beta_h.clone())?;
                let prepared_total_c = PG::prepare_g1(cs.ns(|| "prepared_total_c"), total_c.clone())?;
                let prepared_h = PG::prepare_g2(cs.ns(|| "prepared_h"), verification_key.h.clone())?;

                (prepared_total_w, prepared_beta_h, prepared_total_c, prepared_h)
            };

            let lhs = PG::product_of_pairings(cs.ns(|| "lhs"), &[prepared_total_w, prepared_total_c], &[
                prepared_beta_h,
                prepared_h,
            ])?;

            let rhs = &PG::GTGadget::one(cs.ns(|| "rhs"))?;

            lhs.is_eq(rhs)
        }
    }

    #[allow(clippy::type_complexity)]
    fn prepared_check_combinations<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        mut cs: CS,
        prepared_verification_key: &Self::PreparedVerifierKeyVar,
        linear_combinations: &[LinearCombinationVar<
            <TargetCurve as PairingEngine>::Fr,
            <BaseCurve as PairingEngine>::Fr,
        >],
        prepared_commitments: &[Self::PreparedLabeledCommitmentVar],
        query_set: &QuerySetVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
        evaluations: &EvaluationsVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
        proof: &Self::BatchLCProofVar,
        rand_data: &PCCheckRandomDataVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>,
    ) -> Result<Boolean, SynthesisError> {
        let BatchLCProofVar { proofs, .. } = proof;

        let label_comm_map = prepared_commitments
            .iter()
            .map(|c| (c.label.clone(), c))
            .collect::<BTreeMap<_, _>>();

        let mut lc_info = Vec::new();
        let mut evaluations = evaluations.clone();

        // For each linear combination, we sum up the relevant commitments, multiplied
        // with their corresponding coefficients; these combined commitments are then
        // the inputs to the normal batch check.
        for (i, lc) in linear_combinations.iter().enumerate() {
            let lc_label = lc.label.clone();
            let num_polys = lc.terms.len();

            let mut coeffs_and_comms = Vec::new();

            for (j, (coeff, label)) in lc.terms.iter().enumerate() {
                if label.is_one() {
                    for (label, ref mut eval) in evaluations.0.iter_mut() {
                        if label.name == lc_label {
                            match coeff.clone() {
                                LinearCombinationCoeffVar::One => {
                                    let one = NonNativeFieldVar::one(cs.ns(|| format!("coeff_one_{}_{}", i, j)))?;
                                    **eval = (**eval).sub(cs.ns(|| format!("eval_minus_one_{}_{}", i, j)), &one)?;
                                }
                                LinearCombinationCoeffVar::MinusOne => {
                                    let one = NonNativeFieldVar::one(cs.ns(|| format!("coeff_one_{}_{}", i, j)))?;
                                    **eval = (**eval).add(cs.ns(|| format!("eval_add_one_{}_{}", i, j)), &one)?;
                                }
                                LinearCombinationCoeffVar::Var(variable) => {
                                    **eval =
                                        (**eval).add(cs.ns(|| format!("eval_minus_variable_{}_{}", i, j)), &variable)?
                                }
                            };
                        }
                    }
                } else {
                    let label: &String = label.try_into().unwrap();
                    let &cur_comm = label_comm_map.get(label).unwrap();
                    let negate = match coeff {
                        LinearCombinationCoeffVar::One | LinearCombinationCoeffVar::Var(_) => false,
                        LinearCombinationCoeffVar::MinusOne => true,
                    };

                    if num_polys == 1 && cur_comm.degree_bound.is_some() {
                        assert!(!negate);
                    }

                    let coeff = match coeff {
                        LinearCombinationCoeffVar::One => {
                            Some(NonNativeFieldVar::one(cs.ns(|| format!("coeff_zero_{}_{}", i, j)))?)
                        }
                        LinearCombinationCoeffVar::MinusOne => {
                            let zero = NonNativeFieldVar::zero(cs.ns(|| format!("coeff_zero_{}_{}", i, j)))?;
                            let one = NonNativeFieldVar::one(cs.ns(|| format!("coeff_one_{}_{}", i, j)))?;
                            Some(zero.sub(cs.ns(|| format!("zero_minus_one_{}_{}", i, j)), &one)?)
                        }
                        LinearCombinationCoeffVar::Var(variable) => Some(variable.clone()),
                    };

                    coeffs_and_comms.push((
                        coeff.clone(),
                        cur_comm.degree_bound.clone(),
                        cur_comm.prepared_commitment.clone(),
                        negate,
                    ));
                }
            }

            lc_info.push((lc_label, coeffs_and_comms));
        }

        Self::prepared_batch_check_evaluations(
            cs,
            prepared_verification_key,
            lc_info.as_slice(),
            &query_set,
            &evaluations,
            proofs,
            &rand_data.opening_challenges,
            &rand_data.opening_challenges_bits,
            &rand_data.batching_rands,
            &rand_data.batching_rands_bits,
        )
    }

    fn create_labeled_commitment(
        label: String,
        commitment: Self::CommitmentVar,
        degree_bound: Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
    ) -> Self::LabeledCommitmentVar {
        Self::LabeledCommitmentVar {
            label,
            commitment,
            degree_bound,
        }
    }

    fn create_prepared_labeled_commitment(
        label: String,
        prepared_commitment: Self::PreparedCommitmentVar,
        degree_bound: Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
    ) -> Self::PreparedLabeledCommitmentVar {
        Self::PreparedLabeledCommitmentVar {
            label,
            prepared_commitment,
            degree_bound,
        }
    }
}
