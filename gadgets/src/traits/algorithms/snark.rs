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

use core::fmt::Debug;

use snarkvm_algorithms::traits::SNARK;
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    bits::{Boolean, ToBitsBEGadget, ToBytesGadget},
    traits::alloc::{AllocBytesGadget, AllocGadget},
};

pub enum RandProvider<F: Field> {
    PowerSeries(F)
}

impl<F: Field> RandProvider<F> {
    pub fn output_random_elements(&self, num: usize) -> Vec<F> {
        let mut res = Vec::new();

        match self {
            RandProvider::PowerSeries(challenge) => {
                let mut cur = F::one();
                res.push(cur);

                for _ in 1..num {
                    cur *= challenge;
                    res.push(cur)
                }
            }
        }

        res
    }
}

pub trait PrepareToGadget<T, F: Field> : Sized {
    fn prepare<CS: ConstraintSystem<F>>(&self, cs : CS) -> Result<T, SynthesisError>;
}

pub trait SNARKVerifierGadget<N: SNARK, F: Field> {
    type PreparedVerificationKeyGadget: AllocGadget<N::PreparedVerifyingKey, F>;
    type VerificationKeyGadget: AllocGadget<N::VerifyingKey, F> + AllocBytesGadget<Vec<u8>, F> + ToBytesGadget<F> + PrepareToGadget<Self::PreparedVerificationKeyGadget, F>;
    type ProofGadget: AllocGadget<N::Proof, F> + AllocBytesGadget<Vec<u8>, F>;
    type Input: ToBitsBEGadget<F> + Clone + ?Sized;

    fn check_verify_with_processed_vk<CS: ConstraintSystem<F>, I: Iterator<Item = Self::Input>>(
        cs: CS,
        processed_verification_key: &Self::PreparedVerificationKeyGadget,
        input: I,
        proof: &Self::ProofGadget,
    ) -> Result<(), SynthesisError>;

    fn check_verify<'a, CS: ConstraintSystem<F>, I: Iterator<Item = Self::Input>>(
        mut cs: CS,
        verification_key: &Self::VerificationKeyGadget,
        input: I,
        proof: &Self::ProofGadget,
    ) -> Result<(), SynthesisError> {
        let processed_verification_key = verification_key.prepare(&mut cs.ns(||"prepare the verification key"))?;
        Self::check_verify_with_processed_vk(&mut cs.ns(|| "verify with the processed key"), &processed_verification_key, input, proof)
    }

    fn batch_check_verify_same_processed_vk<'a, CS: ConstraintSystem<F>>(
        mut cs: CS,
        processed_verification_key: &Self::PreparedVerificationKeyGadget,
        inputs: &[Vec<Self::Input>],
        proofs: &[Self::ProofGadget],
        _rand: &RandProvider<F>,
    ) -> Result<(), SynthesisError> {
        assert_eq!(inputs.len(), proofs.len());
        for (i, (input, proof)) in inputs.iter().zip(proofs.iter()).enumerate() {
            Self::check_verify_with_processed_vk(&mut cs.ns(|| format!("verify proof {}", i)), processed_verification_key, (*input).iter().cloned(), proof)?;
        }
        Ok(())
    }

    fn batch_check_verify_same_vk<'a, CS: ConstraintSystem<F>>(
        mut cs: CS,
        verification_key: &Self::VerificationKeyGadget,
        inputs: &[Vec<Self::Input>],
        proofs: &[Self::ProofGadget],
        rand: &RandProvider<F>,
    ) -> Result<(), SynthesisError> {
        let processed_verification_key = verification_key.prepare(&mut cs.ns(||"prepare the verification key"))?;
        Self::batch_check_verify_same_processed_vk(&mut cs.ns(|| "verify with the processed key"), &processed_verification_key, inputs, proofs, rand)
    }

    fn batch_check_verify_different_processed_vk<'a, CS: ConstraintSystem<F>>(
        mut cs: CS,
        processed_verification_keys: &[Self::PreparedVerificationKeyGadget],
        inputs: &[Vec<Self::Input>],
        proofs: &[Self::ProofGadget],
        _rand: &RandProvider<F>,
    ) -> Result<(), SynthesisError> {
        assert_eq!(processed_verification_keys.len(), inputs.len());
        assert_eq!(inputs.len(), proofs.len());
        for (i, ((processed_verification_key, input), proof)) in processed_verification_keys.iter().zip(inputs.iter()).zip(proofs.iter()).enumerate() {
            Self::check_verify_with_processed_vk(&mut cs.ns(|| format!("verify proof {}", i)), processed_verification_key, (*input).iter().cloned(), proof)?;
        }
        Ok(())
    }

    fn batch_check_verify_different_vk<'a, CS: ConstraintSystem<F>>(
        mut cs: CS,
        verification_keys: &[Self::VerificationKeyGadget],
        inputs: &[Vec<Self::Input>],
        proofs: &[Self::ProofGadget],
        _rand: &RandProvider<F>,
    ) -> Result<(), SynthesisError> {
        assert_eq!(verification_keys.len(), inputs.len());
        assert_eq!(inputs.len(), proofs.len());
        for (i, ((verification_key, input), proof)) in verification_keys.iter().zip(inputs.iter()).zip(proofs.iter()).enumerate() {
            Self::check_verify(&mut cs.ns(|| format!("verify proof {}", i)), verification_key, (*input).iter().cloned(), proof)?;
        }
        Ok(())
    }
}

// TODO (raychu86): Unify with the `SNARK` trait. Currently the `SNARKGadget` is only used for `marlin`.

/// This implements constraints for SNARK verifiers.
pub trait SNARKGadget<F: PrimeField, CF: PrimeField, S: SNARK> {
    type PreparedVerifyingKeyVar: AllocGadget<S::PreparedVerifyingKey, CF> + Clone;
    type VerifyingKeyVar: AllocGadget<S::VerifyingKey, CF> + ToBytesGadget<CF> + Clone;
    type InputVar: AllocGadget<Vec<F>, CF> + Clone; // + FromFieldElementsGadget<F, CF>
    type ProofVar: AllocGadget<S::Proof, CF> + Clone;

    /// Information about the R1CS constraints required to check proofs relative
    /// a given verification key. In the context of a LPCP-based pairing-based SNARK
    /// like that of [[Groth16]](https://eprint.iacr.org/2016/260),
    /// this is independent of the R1CS matrices,
    /// whereas for more "complex" SNARKs like [[Marlin]](https://eprint.iacr.org/2019/1047),
    /// this can encode information about the highest degree of polynomials
    /// required to verify proofs.
    type VerifierSize: PartialOrd + Clone + Debug;

    /// Returns information about the R1CS constraints required to check proofs relative
    /// to the verification key `circuit_vk`.
    fn verifier_size(circuit_vk: &S::VerifyingKey) -> Self::VerifierSize;

    fn verify_with_processed_vk<CS: ConstraintSystem<CF>>(
        cs: CS,
        circuit_pvk: &Self::PreparedVerifyingKeyVar,
        x: &Self::InputVar,
        proof: &Self::ProofVar,
    ) -> Result<Boolean, SynthesisError>;

    fn verify<CS: ConstraintSystem<CF>>(
        cs: CS,
        circuit_vk: &Self::VerifyingKeyVar,
        x: &Self::InputVar,
        proof: &Self::ProofVar,
    ) -> Result<Boolean, SynthesisError>;
}
