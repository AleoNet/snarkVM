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

use crate::kzg10::Proof;

use snarkvm_curves::{AffineCurve, PairingEngine};
use snarkvm_gadgets::traits::{curves::PairingGadget, utilities::alloc::AllocGadget};
use snarkvm_nonnative::NonNativeFieldVar;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError, ToConstraintField};

use core::borrow::Borrow;

/// Gadget for a Marlin-KZG10 proof.
#[allow(clippy::type_complexity)]
pub struct ProofVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> where
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{marlin_pc::MarlinKZG10, LabeledPolynomial, PolynomialCommitment};
    use snarkvm_algorithms::fft::DensePolynomial;
    use snarkvm_curves::{
        bls12_377::{Bls12_377, Fq, Fr},
        bw6_761::BW6_761,
        AffineCurve,
    };
    use snarkvm_gadgets::{
        curves::bls12_377::PairingGadget as Bls12_377PairingGadget,
        traits::utilities::eq::EqGadget,
    };
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::rand::{test_rng, UniformRand};

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
        let random_polynomial = DensePolynomial::<Fr>::rand(SUPPORTED_DEGREE - 1, rng);
        let labeled_polynomial = LabeledPolynomial::new("test_polynomial".to_string(), random_polynomial, None, None);

        let labeled_polynomials = vec![&labeled_polynomial];

        // Construct commitments.
        let (commitments, randomness) = PC::commit(&committer_key, labeled_polynomials.clone(), Some(rng)).unwrap();

        let point = Fr::rand(rng);
        let challenge = Fr::rand(rng);

        let proof = PC::open(
            &committer_key,
            labeled_polynomials,
            &commitments,
            point,
            challenge,
            &randomness,
            Some(rng),
        )
        .unwrap();

        let proof_gadget = ProofVar::<_, BaseCurve, PG>::alloc(cs.ns(|| "alloc_proof"), || Ok(proof)).unwrap();

        let expected_w_gadget =
            <PG as PairingGadget<_, _>>::G1Gadget::alloc(cs.ns(|| "proof_w"), || Ok(proof.w.into_projective()))
                .unwrap();

        expected_w_gadget
            .enforce_equal(cs.ns(|| "enforce_equals_w"), &proof_gadget.w)
            .unwrap();

        assert_eq!(proof.random_v.is_some(), proof_gadget.random_v.is_some());

        if let (Some(random_v), Some(random_v_gadget)) = (proof.random_v, proof_gadget.random_v) {
            let expected_random_v = NonNativeFieldVar::alloc(cs.ns(|| "expected_random_v"), || Ok(random_v)).unwrap();

            expected_random_v
                .enforce_equal(cs.ns(|| "enforce_equal_random_v"), &random_v_gadget)
                .unwrap();
        }

        assert!(cs.is_satisfied());
    }
}
