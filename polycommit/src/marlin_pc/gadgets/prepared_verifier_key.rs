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
    marlin_pc::{gadgets::VerifierKeyVar, PreparedVerifierKey},
    PrepareGadget,
    Vec,
};
use snarkvm_curves::{AffineCurve, PairingEngine};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_gadgets::{
    fields::FpGadget,
    traits::{
        curves::{GroupGadget, PairingGadget},
        fields::FieldGadget,
    },
    utilities::alloc::AllocGadget,
};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use core::borrow::Borrow;

/// Var for the verification key of the Marlin-KZG10 polynomial commitment scheme.
#[allow(clippy::type_complexity)]
pub struct PreparedVerifierKeyVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
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
            let shift_power = self
                .origin_vk
                .as_ref()
                .unwrap()
                .get_shift_power(cs.ns(|| "get_shift_power"), bound);

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
