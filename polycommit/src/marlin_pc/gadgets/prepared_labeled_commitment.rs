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
    marlin_pc::{LabeledCommitmentVar, PreparedCommitmentVar},
    PrepareGadget,
};

use snarkvm_curves::PairingEngine;
use snarkvm_gadgets::{fields::FpGadget, traits::curves::PairingGadget};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError, ToConstraintField};

/// Prepared gadget for a Marlin-KZG10 commitment, with a string label and degree bound.
pub struct PreparedLabeledCommitmentVar<
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
    pub prepared_commitment: PreparedCommitmentVar<TargetCurve, BaseCurve, PG>,
    /// Optionally, a bound on the polynomial degree.
    pub degree_bound: Option<FpGadget<<BaseCurve as PairingEngine>::Fr>>,
}

impl<TargetCurve, BaseCurve, PG> Clone for PreparedLabeledCommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
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
