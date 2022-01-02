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

use snarkvm_curves::PairingEngine;
use snarkvm_gadgets::{
    nonnative::NonNativeFieldVar,
    traits::{alloc::AllocGadget, curves::PairingGadget},
};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use crate::{
    kzg10::Proof,
    marlin_pc::{proof::ProofVar, MarlinKZG10},
    BatchLCProof,
    Vec,
};

/// Gadget for a `BatchLCProof`.
#[allow(clippy::type_complexity)]
pub struct BatchLCProofVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> {
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
        BatchLCProof<<TargetCurve as PairingEngine>::Fr, <TargetCurve as PairingEngine>::Fq, MarlinKZG10<TargetCurve>>,
        <BaseCurve as PairingEngine>::Fr,
    > for BatchLCProofVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<
            BatchLCProof<
                <TargetCurve as PairingEngine>::Fr,
                <TargetCurve as PairingEngine>::Fq,
                MarlinKZG10<TargetCurve>,
            >,
        >,
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
                .enumerate()
                .map(|(i, p)| ProofVar::alloc_constant(cs.ns(|| format!("proof_{}", i)), || Ok(p)).unwrap())
                .collect();

            let evals: Option<
                Vec<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
            > = evaluations.map(|evals_inner| {
                evals_inner
                    .iter()
                    .enumerate()
                    .map(|(i, e)| {
                        NonNativeFieldVar::alloc_constant(cs.ns(|| format!("evaluation_{}", i)), || Ok(e)).unwrap()
                    })
                    .collect()
            });

            Self { proofs, evals }
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<
            BatchLCProof<
                <TargetCurve as PairingEngine>::Fr,
                <TargetCurve as PairingEngine>::Fq,
                MarlinKZG10<TargetCurve>,
            >,
        >,
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
                .enumerate()
                .map(|(i, p)| ProofVar::alloc(cs.ns(|| format!("proof_{}", i)), || Ok(p)).unwrap())
                .collect();

            let evals: Option<
                Vec<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
            > = evaluations.map(|evals_inner| {
                evals_inner
                    .iter()
                    .enumerate()
                    .map(|(i, e)| NonNativeFieldVar::alloc(cs.ns(|| format!("evaluation_{}", i)), || Ok(e)).unwrap())
                    .collect()
            });

            Self { proofs, evals }
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<
            BatchLCProof<
                <TargetCurve as PairingEngine>::Fr,
                <TargetCurve as PairingEngine>::Fq,
                MarlinKZG10<TargetCurve>,
            >,
        >,
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
                .enumerate()
                .map(|(i, p)| ProofVar::alloc_input(cs.ns(|| format!("proof_{}", i)), || Ok(p)).unwrap())
                .collect();

            let evals: Option<
                Vec<NonNativeFieldVar<<TargetCurve as PairingEngine>::Fr, <BaseCurve as PairingEngine>::Fr>>,
            > = evaluations.map(|evals_inner| {
                evals_inner
                    .iter()
                    .enumerate()
                    .map(|(i, e)| {
                        NonNativeFieldVar::alloc_input(cs.ns(|| format!("evaluation_{}", i)), || Ok(e)).unwrap()
                    })
                    .collect()
            });

            Self { proofs, evals }
        })
    }
}

#[cfg(test)]
mod tests {
    use snarkvm_algorithms::fft::DensePolynomial;
    use snarkvm_curves::{
        bls12_377::{Bls12_377, Fq, Fr},
        bw6_761::BW6_761,
        AffineCurve,
    };
    use snarkvm_fields::One;
    use snarkvm_gadgets::{curves::bls12_377::PairingGadget as Bls12_377PairingGadget, traits::eq::EqGadget};
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::rand::{test_rng, UniformRand};

    use crate::{marlin_pc::MarlinKZG10, LabeledPolynomial, LinearCombination, PolynomialCommitment, QuerySet};

    use super::*;

    type PC = MarlinKZG10<Bls12_377>;
    type PG = Bls12_377PairingGadget;
    type BaseCurve = BW6_761;

    const MAX_DEGREE: usize = 383;
    const SUPPORTED_DEGREE: usize = 300;
    const SUPPORTED_HIDING_BOUND: usize = 1;

    #[test]
    fn test_alloc() {
        let rng = &mut test_rng();

        let cs = &mut TestConstraintSystem::<Fq>::new();

        // Construct the universal params.
        let pp = PC::setup(MAX_DEGREE, rng).unwrap();

        // Construct the verifying key.
        let (committer_key, _vk) = PC::trim(&pp, SUPPORTED_DEGREE, SUPPORTED_HIDING_BOUND, None).unwrap();

        // Construct a polynomial.
        let label = "TEST".to_string();

        let random_polynomial = DensePolynomial::<Fr>::rand(SUPPORTED_DEGREE - 1, rng);
        let labeled_polynomial = LabeledPolynomial::new(label.clone(), random_polynomial, None, None);

        let labeled_polynomials = vec![&labeled_polynomial];

        // Construct commitments.
        let (commitments, randomness) = PC::commit(&committer_key, labeled_polynomials.clone(), Some(rng)).unwrap();

        // Set up linear combination values.
        let random_point = Fr::rand(rng);
        let mut lc_s = Vec::new();
        let mut query_set = QuerySet::new();

        let mut lc = LinearCombination::empty(label.clone());
        lc.push((Fr::one(), label.to_string().into()));
        lc_s.push(lc);
        query_set.insert((label, ("rand".into(), random_point.clone())));

        let challenge = Fr::rand(rng);

        // Construct batch lc proof.
        let batch_lc_proof = PC::open_combinations(
            &committer_key,
            &lc_s,
            labeled_polynomials,
            &commitments,
            &query_set,
            challenge,
            &randomness,
            Some(rng),
        )
        .unwrap();

        // Construct batch lc proof gadget.
        let batch_lc_proof_gadget =
            BatchLCProofVar::<_, BaseCurve, PG>::alloc(cs.ns(|| "alloc_batch_lc_proof"), || Ok(batch_lc_proof.clone()))
                .unwrap();

        // Check that the proofs in the batch proof are equivalent.
        for (i, (proof, proof_gadget)) in batch_lc_proof
            .proof
            .iter()
            .zip(batch_lc_proof_gadget.proofs)
            .enumerate()
        {
            let expected_w_gadget =
                <PG as PairingGadget<_, _>>::G1Gadget::alloc(cs.ns(|| format!("proof_w_{}", i)), || {
                    Ok(proof.w.into_projective())
                })
                .unwrap();

            expected_w_gadget
                .enforce_equal(cs.ns(|| format!("enforce_equals_w_{}", i)), &proof_gadget.w)
                .unwrap();

            assert_eq!(proof.random_v.is_some(), proof_gadget.random_v.is_some());

            if let (Some(random_v), Some(random_v_gadget)) = (proof.random_v, proof_gadget.random_v) {
                let expected_random_v =
                    NonNativeFieldVar::alloc(cs.ns(|| format!("expected_random_v_{}", i)), || Ok(random_v)).unwrap();

                expected_random_v
                    .enforce_equal(cs.ns(|| format!("enforce_equal_random_v_{}", i)), &random_v_gadget)
                    .unwrap();
            }
        }

        // Check that the evaluations in the batch proof are equivalent.
        assert_eq!(
            batch_lc_proof.evaluations.is_some(),
            batch_lc_proof_gadget.evals.is_some()
        );

        if let (Some(random_vs), Some(random_v_gadgets)) = (batch_lc_proof.evaluations, batch_lc_proof_gadget.evals) {
            for (i, (random_v, random_v_gadget)) in random_vs.iter().zip(random_v_gadgets).enumerate() {
                let expected_random_v =
                    NonNativeFieldVar::alloc(cs.ns(|| format!("expected_random_v_{}", i)), || Ok(random_v)).unwrap();

                expected_random_v
                    .enforce_equal(cs.ns(|| format!("enforce_equal_random_v_{}", i)), &random_v_gadget)
                    .unwrap();
            }
        }

        assert!(cs.is_satisfied());
    }
}
