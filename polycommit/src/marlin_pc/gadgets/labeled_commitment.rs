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
    marlin_pc::{Commitment, CommitmentVar},
    LabeledCommitment,
};

use snarkvm_curves::PairingEngine;
use snarkvm_gadgets::{fields::FpGadget, traits::curves::PairingGadget, utilities::alloc::AllocGadget};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError, ToConstraintField};

use core::borrow::Borrow;

/// Gadget for a Marlin-KZG10 commitment, with a string label and degree bound.
pub struct LabeledCommitmentVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
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
