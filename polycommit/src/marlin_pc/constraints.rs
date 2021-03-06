use crate::{
    constraints::{
        EvaluationsVar, LabeledPointVar, LinearCombinationCoeffVar, LinearCombinationVar, PCCheckRandomDataVar,
        PCCheckVar, PrepareGadget, QuerySetVar,
    },
    data_structures::LabeledCommitment,
    kzg10::{Proof, VerifierKey as KZG10VerifierKey},
    marlin_pc::{
        data_structures::{Commitment, VerifierKey},
        MarlinKZG10, PreparedCommitment, PreparedVerifierKey,
    },
    BTreeMap, BTreeSet, BatchLCProof, PhantomData, String, ToString, Vec,
};
use snarkvm_curves::traits::PairingEngine;
use snarkvm_fields::{Field, ToConstraintField};
use snarkvm_gadgets::traits::curves::PairingGadget;
use snarkvm_gadgets::utilities::alloc::AllocGadget;
use snarkvm_gadgets::{fields::FpGadget, traits::utilities::boolean::Boolean};
use snarkvm_gadgets::{traits::fields::ToConstraintFieldGadget, traits::utilities::ToBytesGadget};
use snarkvm_nonnative::{NonNativeFieldMulResultVar, NonNativeFieldVar};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use core::borrow::Borrow;
use core::ops::Div;
use core::ops::MulAssign;

// use ark_ec::{CycleEngine, PairingEngine};
// use ark_ff::{fields::Field, PrimeField, ToConstraintField};
// use ark_nonnative_field::{NonNativeFieldMulResultVar, NonNativeFieldVar};
// use ark_poly::UVPolynomial;
// use ark_r1cs_std::{
//     alloc::{AllocGadget, AllocationMode},
//     bits::{boolean::Boolean, uint8::UInt8, ToBitsGadget},
//     eq::EqGadget,
//     fields::{fp::FpGadget, FieldVar},
//     groups::CurveVar,
//     pairing::PairingGadget,
//     select::CondSelectGadget,
//     R1CSVar, ToBytesGadget, ToConstraintFieldGadget,
// };
// use ark_relations::r1cs::{ConstraintSystemRef, Namespace, Result as R1CSResult, SynthesisError};
// use ark_std::{
//     borrow::Borrow, convert::TryInto, marker::PhantomData, ops::Div, ops::MulAssign, vec,
// };

/// Var for the verification key of the Marlin-KZG10 polynomial commitment scheme.
#[allow(clippy::type_complexity)]
pub struct VerifierKeyVar<CycleE: CycleEngine, PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>>
where
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    /// Generator of G1.
    pub g: PG::G1Var,
    /// Generator of G2.
    pub h: PG::G2Var,
    /// Generator of G1, times first monomial.
    pub beta_h: PG::G2Var,
    /// Used for the shift powers associated with different degree bounds.
    pub degree_bounds_and_shift_powers: Option<Vec<(usize, FpGadget<<CycleE::E1 as PairingEngine>::Fr>, PG::G1Var)>>,
}

impl<CycleE, PG> VerifierKeyVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    /// Find the appropriate shift for the degree bound.
    pub fn get_shift_power<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
        bound: &FpGadget<<CycleE::E1 as PairingEngine>::Fr>,
    ) -> Option<PG::G1Var> {
        // Search the bound using PIR
        if self.degree_bounds_and_shift_powers.is_none() {
            None
        } else {
            let degree_bounds_and_shift_powers = self.degree_bounds_and_shift_powers.clone().unwrap();

            let mut pir_vector = vec![false; degree_bounds_and_shift_powers.len()];

            let desired_bound_value = bound.value().unwrap_or_default();

            for (i, (_, this_bound, _)) in degree_bounds_and_shift_powers.iter().enumerate() {
                if this_bound.value().unwrap_or_default().eq(&desired_bound_value) {
                    pir_vector[i] = true;
                    break;
                }
            }

            let mut pir_vector_gadgets = Vec::new();
            for bit in pir_vector.iter() {
                pir_vector_gadgets.push(Boolean::new_witness(ark_relations::ns!(cs, "alloc_pir"), || Ok(bit)).unwrap());
            }

            // Sum of the PIR values are equal to one
            let mut sum = FpGadget::<<CycleE::E1 as PairingEngine>::Fr>::zero();
            let one = FpGadget::<<CycleE::E1 as PairingEngine>::Fr>::one();
            for pir_gadget in pir_vector_gadgets.iter() {
                sum += &FpGadget::<<CycleE::E1 as PairingEngine>::Fr>::from(pir_gadget.clone());
            }
            sum.enforce_equal(&one).unwrap();

            // PIR the value
            let mut found_bound = FpGadget::<<CycleE::E1 as PairingEngine>::Fr>::zero();

            let mut found_shift_power = PG::G1Var::zero();

            for (pir_gadget, (_, degree, shift_power)) in
                pir_vector_gadgets.iter().zip(degree_bounds_and_shift_powers.iter())
            {
                found_bound = FpGadget::<<CycleE::E1 as PairingEngine>::Fr>::conditionally_select(
                    pir_gadget,
                    degree,
                    &found_bound,
                )
                .unwrap();

                found_shift_power =
                    PG::G1Var::conditionally_select(pir_gadget, shift_power, &found_shift_power).unwrap();
            }

            found_bound.enforce_equal(&bound).unwrap();

            Some(found_shift_power)
        }
    }
}

impl<CycleE, PG> Clone for VerifierKeyVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
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

impl<CycleE, PG> AllocGadget<VerifierKey<CycleE::E2>, <CycleE::E1 as PairingEngine>::Fr> for VerifierKeyVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn new_variable<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>, T>(
        mut cs: CS,
        val: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<VerifierKey<CycleE::E2>>,
    {
        let vk_orig = val()?.borrow().clone();

        let VerifierKey {
            vk,
            degree_bounds_and_shift_powers,
            ..
        } = vk_orig;

        let degree_bounds_and_shift_powers = degree_bounds_and_shift_powers.map(|vec| {
            vec.iter()
                .map(|(s, g)| {
                    (
                        *s,
                        FpGadget::<<CycleE::E1 as PairingEngine>::Fr>::new_variable(
                            ark_relations::ns!(cs, "degree bound"),
                            || Ok(<<CycleE::E1 as PairingEngine>::Fr as From<u128>>::from(*s as u128)),
                            mode,
                        )
                        .unwrap(),
                        PG::G1Var::new_variable(ark_relations::ns!(cs, "pow"), || Ok(*g), mode).unwrap(),
                    )
                })
                .collect()
        });

        let KZG10VerifierKey { g, h, beta_h, .. } = vk;

        let g = PG::G1Var::new_variable(ark_relations::ns!(cs, "g"), || Ok(g), mode)?;
        let h = PG::G2Var::new_variable(ark_relations::ns!(cs, "h"), || Ok(h), mode)?;
        let beta_h = PG::G2Var::new_variable(ark_relations::ns!(cs, "beta_h"), || Ok(beta_h), mode)?;

        Ok(Self {
            g,
            h,
            beta_h,
            degree_bounds_and_shift_powers,
        })
    }
}

impl<CycleE, PG> ToBytesGadget<<CycleE::E1 as PairingEngine>::Fr> for VerifierKeyVar<CycleE, PG>
where
    CycleE: CycleEngine,

    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn to_bytes<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8<<CycleE::E1 as PairingEngine>::Fr>>, SynthesisError> {
        let mut bytes = Vec::new();

        bytes.extend_from_slice(&self.g.to_bytes()?);
        bytes.extend_from_slice(&self.h.to_bytes()?);
        bytes.extend_from_slice(&self.beta_h.to_bytes()?);

        if self.degree_bounds_and_shift_powers.is_some() {
            let degree_bounds_and_shift_powers = self.degree_bounds_and_shift_powers.as_ref().unwrap();
            for (_, degree_bound, shift_power) in degree_bounds_and_shift_powers.iter() {
                bytes.extend_from_slice(&degree_bound.to_bytes()?);
                bytes.extend_from_slice(&shift_power.to_bytes()?);
            }
        }

        Ok(bytes)
    }
}

impl<CycleE, PG> ToConstraintFieldGadget<<CycleE::E1 as PairingEngine>::Fr> for VerifierKeyVar<CycleE, PG>
where
    CycleE: CycleEngine,

    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    PG::G1Var: ToConstraintFieldGadget<<CycleE::E1 as PairingEngine>::Fr>,
    PG::G2Var: ToConstraintFieldGadget<<CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn to_constraint_field(&self) -> Result<Vec<FpGadget<<CycleE::E1 as PairingEngine>::Fr>>, SynthesisError> {
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
                let mut d_elems = d_gadget.to_constraint_field()?;
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
pub struct PreparedVerifierKeyVar<CycleE: CycleEngine, PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>>
where
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    /// Generator of G1.
    pub prepared_g: Vec<PG::G1Var>,
    /// Generator of G2.
    pub prepared_h: PG::G2PreparedVar,
    /// Generator of G1, times first monomial.
    pub prepared_beta_h: PG::G2PreparedVar,
    /// Used for the shift powers associated with different degree bounds.
    pub prepared_degree_bounds_and_shift_powers:
        Option<Vec<(usize, FpGadget<<CycleE::E1 as PairingEngine>::Fr>, Vec<PG::G1Var>)>>,
    /// Indicate whether or not it is a constant allocation (which decides whether or not shift powers are precomputed)
    pub constant_allocation: bool,
    /// If not a constant allocation, the original vk is attached (for computing the shift power series)
    pub origin_vk: Option<VerifierKeyVar<CycleE, PG>>,
}

impl<CycleE, PG> PreparedVerifierKeyVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    /// Find the appropriate shift for the degree bound.
    pub fn get_shift_power<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
        bound: &FpGadget<<CycleE::E1 as PairingEngine>::Fr>,
    ) -> Option<Vec<PG::G1Var>> {
        if self.constant_allocation {
            if self.prepared_degree_bounds_and_shift_powers.is_none() {
                None
            } else {
                let prepared_degree_bounds_and_shift_powers =
                    self.prepared_degree_bounds_and_shift_powers.as_ref().unwrap();
                let bound_value = bound.value().unwrap_or_default();

                for (_, bound, prepared_shift_powers) in prepared_degree_bounds_and_shift_powers.iter() {
                    if bound.value().unwrap_or_default() == bound_value {
                        return Some((*prepared_shift_powers).clone());
                    }
                }

                None
            }
        } else {
            let shift_power = self.origin_vk.as_ref().unwrap().get_shift_power(cs, bound);

            if let Some(shift_power) = shift_power {
                let mut prepared_shift_gadgets = Vec::<PG::G1Var>::new();

                let supported_bits = <CycleE::E2 as PairingEngine>::Fr::size_in_bits();

                let mut cur: PG::G1Var = shift_power;
                for _ in 0..supported_bits {
                    prepared_shift_gadgets.push(cur.clone());
                    cur.double_in_place().unwrap();
                }

                Some(prepared_shift_gadgets)
            } else {
                None
            }
        }
    }
}

impl<CycleE, PG> PrepareGadget<VerifierKeyVar<CycleE, PG>, <CycleE::E1 as PairingEngine>::Fr>
    for PreparedVerifierKeyVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn prepare(unprepared: &VerifierKeyVar<CycleE, PG>) -> Result<Self, SynthesisError> {
        let supported_bits = <<CycleE::E2 as PairingEngine>::Fr as PrimeField>::size_in_bits();
        let mut prepared_g = Vec::<PG::G1Var>::new();

        let mut g: PG::G1Var = unprepared.g.clone();
        for _ in 0..supported_bits {
            prepared_g.push(g.clone());
            g.double_in_place()?;
        }

        let prepared_h = PG::prepare_g2(&unprepared.h)?;
        let prepared_beta_h = PG::prepare_g2(&unprepared.beta_h)?;

        let prepared_degree_bounds_and_shift_powers = if unprepared.degree_bounds_and_shift_powers.is_some() {
            let mut res = Vec::<(usize, FpGadget<<CycleE::E1 as PairingEngine>::Fr>, Vec<PG::G1Var>)>::new();

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

impl<CycleE, PG> Clone for PreparedVerifierKeyVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
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

impl<CycleE, PG> AllocGadget<PreparedVerifierKey<CycleE::E2>, <CycleE::E1 as PairingEngine>::Fr>
    for PreparedVerifierKeyVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn new_variable<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>, T>(
        mut cs: CS,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<PreparedVerifierKey<CycleE::E2>>,
    {
        let t = f()?;
        let obj = t.borrow();

        let ns = cs.into();
        let cs = ns.cs();

        let mut prepared_g = Vec::<PG::G1Var>::new();
        for g in obj.prepared_vk.prepared_g.iter() {
            prepared_g.push(<PG::G1Var as AllocGadget<
                <CycleE::E2 as PairingEngine>::G1Affine,
                <CycleE::E1 as PairingEngine>::Fr,
            >>::new_variable(
                ark_relations::ns!(cs, "g"), || Ok(*g), mode
            )?);
        }

        let prepared_h =
            PG::G2PreparedVar::new_variable(ark_relations::ns!(cs, "h"), || Ok(&obj.prepared_vk.prepared_h), mode)?;
        let prepared_beta_h = PG::G2PreparedVar::new_variable(
            ark_relations::ns!(cs, "beta_h"),
            || Ok(&obj.prepared_vk.prepared_beta_h),
            mode,
        )?;

        let prepared_degree_bounds_and_shift_powers = if obj.prepared_degree_bounds_and_shift_powers.is_some() {
            let mut res = Vec::<(usize, FpGadget<<CycleE::E1 as PairingEngine>::Fr>, Vec<PG::G1Var>)>::new();

            for (d, shift_power_elems) in obj.prepared_degree_bounds_and_shift_powers.as_ref().unwrap().iter() {
                let mut gadgets = Vec::<PG::G1Var>::new();
                for shift_power_elem in shift_power_elems.iter() {
                    gadgets.push(<PG::G1Var as AllocGadget<
                        <CycleE::E2 as PairingEngine>::G1Affine,
                        <CycleE::E1 as PairingEngine>::Fr,
                    >>::new_variable(
                        cs.clone(), || Ok(shift_power_elem), mode
                    )?);
                }

                let d_gadget = FpGadget::<<CycleE::E1 as PairingEngine>::Fr>::new_variable(
                    cs.clone(),
                    || Ok(<<CycleE::E1 as PairingEngine>::Fr as From<u128>>::from(*d as u128)),
                    mode,
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
pub struct CommitmentVar<CycleE: CycleEngine, PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>>
where
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    comm: PG::G1Var,
    shifted_comm: Option<PG::G1Var>,
}

impl<CycleE, PG> Clone for CommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,

    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn clone(&self) -> Self {
        Self {
            comm: self.comm.clone(),
            shifted_comm: self.shifted_comm.clone(),
        }
    }
}

impl<CycleE, PG> AllocGadget<Commitment<CycleE::E2>, <CycleE::E1 as PairingEngine>::Fr> for CommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,

    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn new_variable<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>, T>(
        mut cs: CS,
        value_gen: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<Commitment<CycleE::E2>>,
    {
        value_gen().and_then(|commitment| {
            let ns = cs.into();
            let cs = ns.cs();

            let commitment = *commitment.borrow();
            let comm = commitment.comm;
            let comm_gadget = PG::G1Var::new_variable(cs.clone(), || Ok(comm.0), mode)?;

            let shifted_comm = commitment.shifted_comm;
            let shifted_comm_gadget = if let Some(shifted_comm) = shifted_comm {
                Some(PG::G1Var::new_variable(cs, || Ok(shifted_comm.0), mode)?)
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

impl<CycleE, PG> ToConstraintFieldGadget<<CycleE::E1 as PairingEngine>::Fr> for CommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    PG::G1Var: ToConstraintFieldGadget<<CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn to_constraint_field(&self) -> Result<Vec<FpGadget<<CycleE::E1 as PairingEngine>::Fr>>, SynthesisError> {
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

impl<CycleE, PG> ToBytesGadget<<CycleE::E1 as PairingEngine>::Fr> for CommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn to_bytes<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8<<CycleE::E1 as PairingEngine>::Fr>>, SynthesisError> {
        let zero_shifted_comm = PG::G1Var::zero();

        let mut bytes = Vec::new();
        bytes.extend_from_slice(&self.comm.to_bytes()?);

        let shifted_comm = self.shifted_comm.clone().unwrap_or(zero_shifted_comm);
        bytes.extend_from_slice(&shifted_comm.to_bytes()?);
        Ok(bytes)
    }
}

/// Prepared gadget for an optionally hiding Marlin-KZG10 commitment.
/// shifted_comm is not prepared, due to the specific use case.
pub struct PreparedCommitmentVar<CycleE: CycleEngine, PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>>
where
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    prepared_comm: Vec<PG::G1Var>,
    shifted_comm: Option<PG::G1Var>,
}

impl<CycleE, PG> Clone for PreparedCommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn clone(&self) -> Self {
        Self {
            prepared_comm: self.prepared_comm.clone(),
            shifted_comm: self.shifted_comm.clone(),
        }
    }
}

impl<CycleE, PG> PrepareGadget<CommitmentVar<CycleE, PG>, <CycleE::E1 as PairingEngine>::Fr>
    for PreparedCommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn prepare(unprepared: &CommitmentVar<CycleE, PG>) -> Result<Self, SynthesisError> {
        let mut prepared_comm = Vec::<PG::G1Var>::new();
        let supported_bits = <<CycleE::E2 as PairingEngine>::Fr as PrimeField>::size_in_bits();

        let mut cur: PG::G1Var = unprepared.comm.clone();
        for _ in 0..supported_bits {
            prepared_comm.push(cur.clone());
            cur.double_in_place()?;
        }

        Ok(Self {
            prepared_comm,
            shifted_comm: unprepared.shifted_comm.clone(),
        })
    }
}

impl<CycleE, PG> AllocGadget<PreparedCommitment<CycleE::E2>, <CycleE::E1 as PairingEngine>::Fr>
    for PreparedCommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn new_variable<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>, T>(
        mut cs: CS,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<PreparedCommitment<CycleE::E2>>,
    {
        let t = f()?;
        let obj = t.borrow();

        let mut prepared_comm = Vec::<PG::G1Var>::new();

        for comm_elem in obj.prepared_comm.0.iter() {
            prepared_comm.push(<PG::G1Var as AllocGadget<
                <CycleE::E2 as PairingEngine>::G1Projective,
                <CycleE::E1 as PairingEngine>::Fr,
            >>::new_variable(
                ark_relations::ns!(cs, "comm_elem"),
                || {
                    Ok(<<CycleE::E2 as PairingEngine>::G1Projective as From<
                        <CycleE::E2 as PairingEngine>::G1Affine,
                    >>::from(*comm_elem))
                },
                mode,
            )?);
        }

        let shifted_comm = if obj.shifted_comm.is_some() {
            Some(<PG::G1Var as AllocGadget<
                <CycleE::E2 as PairingEngine>::G1Projective,
                <CycleE::E1 as PairingEngine>::Fr,
            >>::new_variable(
                ark_relations::ns!(cs, "shifted_comm"),
                || {
                    Ok(<<CycleE::E2 as PairingEngine>::G1Projective as From<
                        <CycleE::E2 as PairingEngine>::G1Affine,
                    >>::from(obj.shifted_comm.unwrap().0))
                },
                mode,
            )?)
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
pub struct LabeledCommitmentVar<CycleE: CycleEngine, PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>>
where
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    /// A text label for the commitment.
    pub label: String,
    /// The plain commitment.
    pub commitment: CommitmentVar<CycleE, PG>,
    /// Optionally, a bound on the polynomial degree.
    pub degree_bound: Option<FpGadget<<CycleE::E1 as PairingEngine>::Fr>>,
}

impl<CycleE, PG> Clone for LabeledCommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn clone(&self) -> Self {
        LabeledCommitmentVar {
            label: self.label.clone(),
            commitment: self.commitment.clone(),
            degree_bound: self.degree_bound.clone(),
        }
    }
}

impl<CycleE, PG> AllocGadget<LabeledCommitment<Commitment<CycleE::E2>>, <CycleE::E1 as PairingEngine>::Fr>
    for LabeledCommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn new_variable<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>, T>(
        mut cs: CS,
        value_gen: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<LabeledCommitment<Commitment<CycleE::E2>>>,
    {
        value_gen().and_then(|labeled_commitment| {
            let labeled_commitment = labeled_commitment.borrow().clone();
            let label = labeled_commitment.label().to_string();
            let commitment = labeled_commitment.commitment();
            let degree_bound = labeled_commitment.degree_bound();

            let commitment =
                CommitmentVar::new_variable(ark_relations::ns!(cs, "commitment"), || Ok(commitment), mode)?;

            let degree_bound = if let Some(degree_bound) = degree_bound {
                FpGadget::<<CycleE::E1 as PairingEngine>::Fr>::new_variable(
                    ark_relations::ns!(cs, "degree_bound"),
                    || {
                        Ok(<<CycleE::E1 as PairingEngine>::Fr as From<u128>>::from(
                            degree_bound as u128,
                        ))
                    },
                    mode,
                )
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
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
> where
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    /// A text label for the commitment.
    pub label: String,
    /// The plain commitment.
    pub prepared_commitment: PreparedCommitmentVar<CycleE, PG>,
    /// Optionally, a bound on the polynomial degree.
    pub degree_bound: Option<FpGadget<<CycleE::E1 as PairingEngine>::Fr>>,
}

impl<CycleE, PG> Clone for PreparedLabeledCommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn clone(&self) -> Self {
        Self {
            label: self.label.clone(),
            prepared_commitment: self.prepared_commitment.clone(),
            degree_bound: self.degree_bound.clone(),
        }
    }
}

impl<CycleE, PG> PrepareGadget<LabeledCommitmentVar<CycleE, PG>, <CycleE::E1 as PairingEngine>::Fr>
    for PreparedLabeledCommitmentVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn prepare(unprepared: &LabeledCommitmentVar<CycleE, PG>) -> Result<Self, SynthesisError> {
        let prepared_commitment = PreparedCommitmentVar::prepare(&unprepared.commitment)?;

        Ok(Self {
            label: unprepared.label.clone(),
            prepared_commitment,
            degree_bound: unprepared.degree_bound.clone(),
        })
    }
}

/// Var for a Marlin-KZG10 proof.
#[allow(clippy::type_complexity)]
pub struct ProofVar<CycleE: CycleEngine, PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>>
where
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    /// The commitment to the witness polynomial.
    pub w: PG::G1Var,
    /// The evaluation of the random hiding polynomial.
    pub random_v: Option<NonNativeFieldVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>>,
}

impl<CycleE, PG> Clone for ProofVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn clone(&self) -> Self {
        Self {
            w: self.w.clone(),
            random_v: self.random_v.clone(),
        }
    }
}

impl<CycleE, PG> AllocGadget<Proof<CycleE::E2>, <CycleE::E1 as PairingEngine>::Fr> for ProofVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn new_variable<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>, T>(
        mut cs: CS,
        value_gen: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<Proof<CycleE::E2>>,
    {
        value_gen().and_then(|proof| {
            let Proof { w, random_v } = *proof.borrow();
            let w = PG::G1Var::new_variable(ark_relations::ns!(cs, "w"), || Ok(w), mode)?;

            let random_v = match random_v {
                None => None,
                Some(random_v_inner) => Some(NonNativeFieldVar::new_variable(
                    ark_relations::ns!(cs, "random_v"),
                    || Ok(random_v_inner),
                    mode,
                )?),
            };

            Ok(Self { w, random_v })
        })
    }
}

/// An allocated version of `BatchLCProof`.
#[allow(clippy::type_complexity)]
pub struct BatchLCProofVar<CycleE: CycleEngine, PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>>
where
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    /// Evaluation proofs.
    pub proofs: Vec<ProofVar<CycleE, PG>>,
    /// Evaluations required to verify the proof.
    pub evals: Option<Vec<NonNativeFieldVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>>>,
}

impl<CycleE, PG> Clone for BatchLCProofVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn clone(&self) -> Self {
        Self {
            proofs: self.proofs.clone(),
            evals: self.evals.clone(),
        }
    }
}

impl<CycleE, PG>
    AllocGadget<
        BatchLCProof<<CycleE::E2 as PairingEngine>::Fr, P, MarlinKZG10<CycleE::E2>>,
        <CycleE::E1 as PairingEngine>::Fr,
    > for BatchLCProofVar<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn new_variable<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>, T>(
        mut cs: CS,
        value_gen: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>
    where
        T: Borrow<BatchLCProof<<CycleE::E2 as PairingEngine>::Fr, P, MarlinKZG10<CycleE::E2>>>,
    {
        value_gen().map(|proof| {
            let BatchLCProof { proof, evals } = proof.borrow().clone();

            let proofs: Vec<Proof<_>> = proof.to_vec();
            let proofs: Vec<ProofVar<CycleE, PG>> = proofs
                .iter()
                .map(|p| ProofVar::new_variable(ark_relations::ns!(cs, "proof"), || Ok(p), mode).unwrap())
                .collect();

            #[allow(clippy::type_complexity)]
            let evals: Option<
                Vec<NonNativeFieldVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>>,
            > = match evals {
                None => None,
                Some(evals_inner) => Some(
                    evals_inner
                        .iter()
                        .map(|e| {
                            NonNativeFieldVar::new_variable(ark_relations::ns!(cs, "evaluation"), || Ok(e), mode)
                                .unwrap()
                        })
                        .collect(),
                ),
            };

            Self {
                proofs,
                evals,
                polynomial: PhantomData,
            }
        })
    }
}

/// Var for the Marlin-KZG10 polynomial commitment verifier.
pub struct MarlinKZG10Gadget<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    _cycle_engine: PhantomData<CycleE>,
    _pairing_gadget: PhantomData<PG>,
}

impl<CycleE, PG> Clone for MarlinKZG10Gadget<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    fn clone(&self) -> Self {
        Self {
            _cycle_engine: PhantomData,
            _pairing_gadget: PhantomData,
        }
    }
}

impl<CycleE, PG> MarlinKZG10Gadget<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn prepared_batch_check_evaluations<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>>(
        cs: CS,
        prepared_verification_key: &<Self as PCCheckVar<
            <CycleE::E2 as PairingEngine>::Fr,
            P,
            MarlinKZG10<CycleE::E2>,
            <CycleE::E1 as PairingEngine>::Fr,
        >>::PreparedVerifierKeyVar,
        lc_info: &[(
            String,
            Vec<(
                Option<NonNativeFieldVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>>,
                Option<FpGadget<<CycleE::E1 as PairingEngine>::Fr>>,
                PreparedCommitmentVar<CycleE, PG>,
                bool,
            )>,
        )],
        query_set: &QuerySetVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>,
        evaluations: &EvaluationsVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>,
        proofs: &[<Self as PCCheckVar<
            <CycleE::E2 as PairingEngine>::Fr,
            P,
            MarlinKZG10<CycleE::E2>,
            <CycleE::E1 as PairingEngine>::Fr,
        >>::ProofVar],
        opening_challenges: &[NonNativeFieldVar<
            <CycleE::E2 as PairingEngine>::Fr,
            <CycleE::E1 as PairingEngine>::Fr,
        >],
        opening_challenges_bits: &[Vec<Boolean>],
        batching_rands: &[NonNativeFieldVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>],
        batching_rands_bits: &[Vec<Boolean>],
    ) -> Result<Boolean, SynthesisError> {
        let mut batching_rands = batching_rands.to_vec();
        let mut batching_rands_bits = batching_rands_bits.to_vec();

        let commitment_lcs: BTreeMap<
            String,
            (
                String,
                Vec<(
                    Option<NonNativeFieldVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>>,
                    Option<FpGadget<<CycleE::E1 as PairingEngine>::Fr>>,
                    PreparedCommitmentVar<CycleE, PG>,
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
        for (_, (point, labels)) in query_to_labels_map.into_iter() {
            let mut comms_to_combine = Vec::<
                Vec<(
                    Option<NonNativeFieldVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>>,
                    Option<FpGadget<<CycleE::E1 as PairingEngine>::Fr>>,
                    PreparedCommitmentVar<CycleE, PG>,
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
            let mut combined_comm = PG::G1Var::zero();
            let mut combined_eval = NonNativeFieldMulResultVar::<
                <CycleE::E2 as PairingEngine>::Fr,
                <CycleE::E1 as PairingEngine>::Fr,
            >::zero();

            let mut opening_challenges_counter = 0;

            for (commitment_lcs, value) in comms_to_combine.into_iter().zip(values_to_combine) {
                let challenge = opening_challenges[opening_challenges_counter].clone();

                let challenge_bits = opening_challenges_bits[opening_challenges_counter].clone();
                opening_challenges_counter += 1;

                for (coeff, degree_bound, comm, negate) in commitment_lcs.iter() {
                    let PreparedCommitmentVar { shifted_comm, .. } = comm;

                    if coeff.is_none() {
                        // To combine the commitments, we multiply each by one of the random challenges, and sum.
                        let mut comm_times_challenge = PG::G1Var::zero();
                        {
                            for (bit, base_power) in challenge_bits.iter().zip(comm.prepared_comm.iter()) {
                                let mut new_encoded = base_power.clone();
                                new_encoded += comm_times_challenge.clone();
                                comm_times_challenge =
                                    PG::G1Var::conditionally_select(bit, &new_encoded, &comm_times_challenge)?;
                            }
                        }

                        if negate.eq(&true) {
                            comm_times_challenge = comm_times_challenge.negate()?;
                        }

                        combined_comm += comm_times_challenge.clone();

                        // If the degree bound is specified, we include the adjusted degree-shifted commitment
                        // (that is, c_i' - v_i beta^{D - d_i} G), where d_i is the specific degree bound and
                        // v_i is the evaluation, in the combined commitment,
                        if let Some(degree_bound) = degree_bound {
                            let challenge_shifted_bits = opening_challenges_bits[opening_challenges_counter].clone();
                            opening_challenges_counter += 1;

                            let mut shifted_comm = shifted_comm.clone().unwrap();

                            if negate.eq(&true) {
                                shifted_comm = shifted_comm.negate()?;
                            }

                            let value_bits = value.to_bits_le()?;
                            let shift_power = prepared_verification_key
                                .get_shift_power(cs.clone(), degree_bound)
                                .unwrap();

                            let mut shift_power_times_value = PG::G1Var::zero();
                            {
                                for (bit, base_power) in value_bits.iter().zip(&shift_power) {
                                    let mut new_encoded = base_power.clone();
                                    new_encoded += shift_power_times_value.clone();
                                    shift_power_times_value =
                                        PG::G1Var::conditionally_select(bit, &new_encoded, &shift_power_times_value)?;
                                }
                            }
                            let mut adjusted_comm = shifted_comm;
                            adjusted_comm -= shift_power_times_value;
                            let adjusted_comm_times_challenge =
                                adjusted_comm.scalar_mul_le(challenge_shifted_bits.iter())?;
                            combined_comm += adjusted_comm_times_challenge;
                        }
                    } else {
                        assert!(degree_bound.is_none());

                        let mut comm_times_challenge = PG::G1Var::zero();
                        let coeff = coeff.clone().unwrap();

                        let challenge_times_coeff = &challenge * &coeff;
                        let challenge_times_coeff_bits = challenge_times_coeff.to_bits_le()?;

                        {
                            for (bit, base_power) in challenge_times_coeff_bits.iter().zip(&comm.prepared_comm) {
                                let mut new_encoded = comm_times_challenge.clone();
                                new_encoded += base_power.clone();
                                comm_times_challenge =
                                    PG::G1Var::conditionally_select(bit, &new_encoded, &comm_times_challenge)?;
                            }
                        }

                        if negate.eq(&true) {
                            comm_times_challenge = comm_times_challenge.negate()?;
                        }

                        combined_comm += comm_times_challenge;
                    }
                }
                // Similarly, we add up the evaluations, multiplied with random challenges.
                let value_times_challenge_unreduced = value.mul_without_reduce(&challenge)?;

                combined_eval += &value_times_challenge_unreduced;
            }

            let combined_eval_reduced = combined_eval.reduce()?;

            combined_queries.push(point.clone());
            combined_comms.push(combined_comm);
            combined_evals.push(combined_eval_reduced);
        }

        println!("before PC batch check: constraints: {}", cs.num_constraints());

        // Perform the batch check.
        {
            let mut total_c = PG::G1Var::zero();
            let mut total_w = PG::G1Var::zero();

            let mut g_multiplier = NonNativeFieldMulResultVar::<
                <CycleE::E2 as PairingEngine>::Fr,
                <CycleE::E1 as PairingEngine>::Fr,
            >::zero();
            let mut g_multiplier_reduced =
                NonNativeFieldVar::<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>::zero();
            for (i, (((c, z), v), proof)) in combined_comms
                .iter()
                .zip(combined_queries)
                .zip(combined_evals)
                .zip(proofs)
                .enumerate()
            {
                let z_bits = z.to_bits_le()?;

                let w_times_z = proof.w.scalar_mul_le(z_bits.iter())?;

                let mut c_plus_w_times_z = c.clone();
                c_plus_w_times_z += w_times_z;

                if i != 0 {
                    let randomizer = batching_rands.remove(0);
                    let randomizer_bits = batching_rands_bits.remove(0);

                    let randomizer_times_v = randomizer.mul_without_reduce(&v)?;

                    g_multiplier += &randomizer_times_v;

                    let c_times_randomizer = c_plus_w_times_z.scalar_mul_le(randomizer_bits.iter())?;
                    let w_times_randomizer = proof.w.scalar_mul_le(randomizer_bits.iter())?;
                    total_c += c_times_randomizer;
                    total_w += w_times_randomizer;
                } else {
                    g_multiplier_reduced += v;
                    total_c += c_plus_w_times_z;
                    total_w += proof.w.clone();
                }
            }

            // Prepare each input to the pairing.
            let (prepared_total_w, prepared_beta_h, prepared_total_c, prepared_h) = {
                let g_multiplier_reduced = g_multiplier.reduce()? + &g_multiplier_reduced;
                let g_multiplier_bits = g_multiplier_reduced.to_bits_le()?;

                let mut g_times_mul = PG::G1Var::zero();
                {
                    for (bit, base_power) in g_multiplier_bits.iter().zip(&prepared_verification_key.prepared_g) {
                        let mut new_encoded = g_times_mul.clone();
                        new_encoded += base_power.clone();
                        g_times_mul = PG::G1Var::conditionally_select(bit, &new_encoded, &g_times_mul)?;
                    }
                }
                total_c -= g_times_mul;
                total_w = total_w.negate()?;

                let prepared_total_w = PG::prepare_g1(&total_w)?;
                let prepared_beta_h = prepared_verification_key.prepared_beta_h.clone();
                let prepared_total_c = PG::prepare_g1(&total_c)?;
                let prepared_h = prepared_verification_key.prepared_h.clone();

                (prepared_total_w, prepared_beta_h, prepared_total_c, prepared_h)
            };

            let lhs = PG::product_of_pairings(&[prepared_total_w, prepared_total_c], &[prepared_beta_h, prepared_h])?;

            println!("after PC batch check: constraints: {}", cs.num_constraints());

            let rhs = &PG::GTVar::one();
            lhs.is_eq(&rhs)
        }
    }
}

impl<CycleE, PG>
    PCCheckVar<<CycleE::E2 as PairingEngine>::Fr, P, MarlinKZG10<CycleE::E2>, <CycleE::E1 as PairingEngine>::Fr>
    for MarlinKZG10Gadget<CycleE, PG>
where
    CycleE: CycleEngine,
    PG: PairingGadget<CycleE::E2, <CycleE::E1 as PairingEngine>::Fr>,
    <CycleE::E2 as PairingEngine>::G1Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G2Projective: MulAssign<<CycleE::E1 as PairingEngine>::Fq>,
    <CycleE::E2 as PairingEngine>::G1Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
    <CycleE::E2 as PairingEngine>::G2Affine:
        ToConstraintField<<<CycleE::E1 as PairingEngine>::Fr as Field>::BasePrimeField>,
{
    type VerifierKeyVar = VerifierKeyVar<CycleE, PG>;
    type PreparedVerifierKeyVar = PreparedVerifierKeyVar<CycleE, PG>;
    type CommitmentVar = CommitmentVar<CycleE, PG>;
    type PreparedCommitmentVar = PreparedCommitmentVar<CycleE, PG>;
    type LabeledCommitmentVar = LabeledCommitmentVar<CycleE, PG>;
    type PreparedLabeledCommitmentVar = PreparedLabeledCommitmentVar<CycleE, PG>;
    type ProofVar = ProofVar<CycleE, PG>;
    type BatchLCProofVar = BatchLCProofVar<CycleE, PG>;

    #[allow(clippy::type_complexity)]
    fn batch_check_evaluations<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>>(
        _cs: CS,
        verification_key: &Self::VerifierKeyVar,
        commitments: &[Self::LabeledCommitmentVar],
        query_set: &QuerySetVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>,
        evaluations: &EvaluationsVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>,
        proofs: &[Self::ProofVar],
        rand_data: &PCCheckRandomDataVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>,
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
            let mut combined_comm = PG::G1Var::zero();
            let mut combined_eval = NonNativeFieldMulResultVar::<
                <CycleE::E2 as PairingEngine>::Fr,
                <CycleE::E1 as PairingEngine>::Fr,
            >::zero();

            let mut opening_challenges_counter = 0;

            for (labeled_commitment, value) in comms_to_combine.into_iter().zip(values_to_combine.iter()) {
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
                combined_comm += commitment.comm.scalar_mul_le(challenge_bits.iter())?;

                // Similarly, we add up the evaluations, multiplied with random challenges.
                let value_times_challenge_unreduced = value.mul_without_reduce(&challenge)?;
                combined_eval += &value_times_challenge_unreduced;

                // If the degree bound is specified, we include the adjusted degree-shifted commitment
                // (that is, c_i' - v_i beta^{D - d_i} G), where d_i is the specific degree bound and
                // v_i is the evaluation, in the cocmbined commitment,
                if let Some(degree_bound) = degree_bound {
                    let challenge_shifted_bits = rand_data.opening_challenges_bits[opening_challenges_counter].clone();
                    opening_challenges_counter += 1;

                    let shifted_comm = shifted_comm.as_ref().unwrap().clone();

                    let value_bits = value.to_bits_le()?;
                    let shift_power = verification_key
                        .get_shift_power(verification_key.g.cs(), &degree_bound)
                        .unwrap();

                    let shift_power_times_value = shift_power.scalar_mul_le(value_bits.iter())?;
                    let mut adjusted_comm = shifted_comm;
                    adjusted_comm -= shift_power_times_value;

                    let adjusted_comm_times_challenge = adjusted_comm.scalar_mul_le(challenge_shifted_bits.iter())?;

                    combined_comm += adjusted_comm_times_challenge;
                }
            }

            combined_queries.push(point.clone());
            combined_comms.push(combined_comm);
            combined_evals.push(combined_eval);
        }

        // Perform the batch check.
        {
            let mut total_c = PG::G1Var::zero();
            let mut total_w = PG::G1Var::zero();

            let mut g_multiplier = NonNativeFieldMulResultVar::<
                <CycleE::E2 as PairingEngine>::Fr,
                <CycleE::E1 as PairingEngine>::Fr,
            >::zero();
            for (((c, z), v), proof) in combined_comms
                .iter()
                .zip(combined_queries)
                .zip(combined_evals)
                .zip(proofs)
            {
                let z_bits = z.to_bits_le()?;

                let w_times_z = proof.w.scalar_mul_le(z_bits.iter())?;
                let mut c_plus_w_times_z = c.clone();
                c_plus_w_times_z += w_times_z;

                let randomizer = batching_rands.remove(0);
                let randomizer_bits = batching_rands_bits.remove(0);

                let v_reduced = v.reduce()?;
                let randomizer_times_v = randomizer.mul_without_reduce(&v_reduced)?;

                g_multiplier += randomizer_times_v;

                let c_times_randomizer = c_plus_w_times_z.scalar_mul_le(randomizer_bits.iter())?;
                let w_times_randomizer = proof.w.scalar_mul_le(randomizer_bits.iter())?;
                total_c += c_times_randomizer;
                total_w += w_times_randomizer;
            }

            // Prepare each input to the pairing.
            let (prepared_total_w, prepared_beta_h, prepared_total_c, prepared_h) = {
                let g_multiplier_reduced = g_multiplier.reduce()?;
                let g_multiplier_bits = g_multiplier_reduced.to_bits_le()?;

                let g_times_mul = verification_key.g.scalar_mul_le(g_multiplier_bits.iter())?;
                total_c -= g_times_mul;
                total_w = total_w.negate()?;

                let prepared_total_w = PG::prepare_g1(&total_w)?;
                let prepared_beta_h = PG::prepare_g2(&verification_key.beta_h)?;
                let prepared_total_c = PG::prepare_g1(&total_c)?;
                let prepared_h = PG::prepare_g2(&verification_key.h)?;

                (prepared_total_w, prepared_beta_h, prepared_total_c, prepared_h)
            };

            let lhs = PG::product_of_pairings(&[prepared_total_w, prepared_total_c], &[prepared_beta_h, prepared_h])?;

            let rhs = &PG::GTVar::one();

            lhs.is_eq(rhs)
        }
    }

    #[allow(clippy::type_complexity)]
    fn prepared_check_combinations<CS: ConstraintSystem<<CycleE::E1 as PairingEngine>::Fr>>(
        cs: CS,
        prepared_verification_key: &Self::PreparedVerifierKeyVar,
        linear_combinations: &[LinearCombinationVar<
            <CycleE::E2 as PairingEngine>::Fr,
            <CycleE::E1 as PairingEngine>::Fr,
        >],
        prepared_commitments: &[Self::PreparedLabeledCommitmentVar],
        query_set: &QuerySetVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>,
        evaluations: &EvaluationsVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>,
        proof: &Self::BatchLCProofVar,
        rand_data: &PCCheckRandomDataVar<<CycleE::E2 as PairingEngine>::Fr, <CycleE::E1 as PairingEngine>::Fr>,
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
        for lc in linear_combinations.iter() {
            let lc_label = lc.label.clone();
            let num_polys = lc.terms.len();

            let mut coeffs_and_comms = Vec::new();

            for (coeff, label) in lc.terms.iter() {
                if label.is_one() {
                    for (label, ref mut eval) in evaluations.0.iter_mut() {
                        if label.name == lc_label {
                            match coeff.clone() {
                                LinearCombinationCoeffVar::One => **eval = (**eval).clone() - &NonNativeFieldVar::one(),
                                LinearCombinationCoeffVar::MinusOne => {
                                    **eval = (**eval).clone() + &NonNativeFieldVar::one()
                                }
                                LinearCombinationCoeffVar::Var(variable) => **eval = (**eval).clone() - &variable,
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
                        LinearCombinationCoeffVar::One => Some(NonNativeFieldVar::one()),
                        LinearCombinationCoeffVar::MinusOne => {
                            Some(NonNativeFieldVar::zero() - NonNativeFieldVar::one())
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
        degree_bound: Option<FpGadget<<CycleE::E1 as PairingEngine>::Fr>>,
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
        degree_bound: Option<FpGadget<<CycleE::E1 as PairingEngine>::Fr>>,
    ) -> Self::PreparedLabeledCommitmentVar {
        Self::PreparedLabeledCommitmentVar {
            label,
            prepared_commitment,
            degree_bound,
        }
    }
}
