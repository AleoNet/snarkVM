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
    kzg10::Proof,
    marlin_pc::{proof::ProofVar, MarlinKZG10},
    BatchLCProof,
};

use snarkvm_curves::PairingEngine;
use snarkvm_gadgets::{traits::curves::PairingGadget, utilities::alloc::AllocGadget};
use snarkvm_nonnative::NonNativeFieldVar;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError, ToConstraintField};

use core::borrow::Borrow;

/// Gadget for a `BatchLCProof`.
#[allow(clippy::type_complexity)]
pub struct BatchLCProofVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
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
