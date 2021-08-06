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

use std::{borrow::Borrow, marker::PhantomData};

use snarkvm_algorithms::snark::groth16::{Groth16, Proof, VerifyingKey};
use snarkvm_curves::traits::{AffineCurve, PairingEngine};
use snarkvm_fields::ToConstraintField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    traits::{
        algorithms::snark::SNARKVerifierGadget,
        alloc::AllocGadget,
        curves::{GroupGadget, PairingGadget},
        eq::EqGadget,
    },
    AllocBytesGadget,
    BooleanInputGadget,
    FpGadget,
    PrepareGadget,
    ToBytesGadget,
    ToConstraintFieldGadget,
    UInt8,
};
use snarkvm_utilities::FromBytes;

#[derive(Derivative)]
#[derivative(Clone(bound = "P::G1Gadget: Clone, P::G2Gadget: Clone"))]
pub struct ProofGadget<PairingE: PairingEngine, P: PairingGadget<PairingE>> {
    pub a: P::G1Gadget,
    pub b: P::G2Gadget,
    pub c: P::G1Gadget,
}

#[derive(Derivative)]
#[derivative(Clone(bound = "P::G1Gadget: Clone, P::GTGadget: Clone, P::G1PreparedGadget: Clone, \
             P::G2PreparedGadget: Clone, "))]
pub struct VerifyingKeyGadget<PairingE: PairingEngine, P: PairingGadget<PairingE>> {
    pub alpha_g1: P::G1Gadget,
    pub beta_g2: P::G2Gadget,
    pub gamma_g2: P::G2Gadget,
    pub delta_g2: P::G2Gadget,
    pub gamma_abc_g1: Vec<P::G1Gadget>,
}

impl<PairingE: PairingEngine, P: PairingGadget<PairingE>>
    PrepareGadget<PreparedVerifyingKeyGadget<PairingE, P>, PairingE::Fq> for VerifyingKeyGadget<PairingE, P>
{
    fn prepare<CS: ConstraintSystem<PairingE::Fq>>(
        &self,
        mut cs: CS,
    ) -> Result<PreparedVerifyingKeyGadget<PairingE, P>, SynthesisError> {
        let mut cs = cs.ns(|| "Preparing verifying key");
        let alpha_g1_pc = P::prepare_g1(&mut cs.ns(|| "Prepare alpha_g1"), self.alpha_g1.clone())?;
        let beta_g2_pc = P::prepare_g2(&mut cs.ns(|| "Prepare beta_g2"), self.beta_g2.clone())?;

        let alpha_g1_beta_g2 = P::pairing(
            &mut cs.ns(|| "Precompute e(alpha_g1, beta_g2)"),
            alpha_g1_pc,
            beta_g2_pc,
        )?;

        let gamma_g2_neg = self.gamma_g2.negate(&mut cs.ns(|| "Negate gamma_g2"))?;
        let gamma_g2_neg_pc = P::prepare_g2(&mut cs.ns(|| "Prepare gamma_g2_neg"), gamma_g2_neg)?;

        let delta_g2_neg = self.delta_g2.negate(&mut cs.ns(|| "Negate delta_g2"))?;
        let delta_g2_neg_pc = P::prepare_g2(&mut cs.ns(|| "Prepare delta_g2_neg"), delta_g2_neg)?;

        Ok(PreparedVerifyingKeyGadget {
            alpha_g1_beta_g2,
            gamma_g2_neg_pc,
            delta_g2_neg_pc,
            gamma_abc_g1: self.gamma_abc_g1.clone(),
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone(
    bound = "P::G1Gadget: Clone, P::GTGadget: Clone, P::G1PreparedGadget: Clone, P::G2PreparedGadget: Clone"
))]
pub struct PreparedVerifyingKeyGadget<PairingE: PairingEngine, P: PairingGadget<PairingE>> {
    pub alpha_g1_beta_g2: P::GTGadget,
    pub gamma_g2_neg_pc: P::G2PreparedGadget,
    pub delta_g2_neg_pc: P::G2PreparedGadget,
    pub gamma_abc_g1: Vec<P::G1Gadget>,
}

pub struct Groth16VerifierGadget<PairingE, P>
where
    PairingE: PairingEngine,
    P: PairingGadget<PairingE>,
{
    _pairing_engine: PhantomData<PairingE>,
    _pairing_gadget: PhantomData<P>,
}

impl<PairingE, P, V> SNARKVerifierGadget<Groth16<PairingE, V>> for Groth16VerifierGadget<PairingE, P>
where
    PairingE: PairingEngine,
    V: ToConstraintField<PairingE::Fr>,
    P: PairingGadget<PairingE>,
{
    type InputGadget = BooleanInputGadget<PairingE::Fr, PairingE::Fq>;
    type PreparedVerificationKeyGadget = PreparedVerifyingKeyGadget<PairingE, P>;
    type ProofGadget = ProofGadget<PairingE, P>;
    type VerificationKeyGadget = VerifyingKeyGadget<PairingE, P>;

    fn prepared_check_verify<CS: ConstraintSystem<PairingE::Fq>>(
        mut cs: CS,
        pvk: &Self::PreparedVerificationKeyGadget,
        public_inputs: &Self::InputGadget,
        proof: &Self::ProofGadget,
    ) -> Result<(), SynthesisError> {
        let PreparedVerifyingKeyGadget {
            alpha_g1_beta_g2,
            gamma_g2_neg_pc,
            delta_g2_neg_pc,
            mut gamma_abc_g1,
        } = pvk.clone();

        assert!(public_inputs.val.len() + 1 == gamma_abc_g1.len());

        let mut gamma_abc_g1_iter = gamma_abc_g1.iter_mut();

        let g_ic = {
            let mut cs = cs.ns(|| "Process input");
            let mut g_ic = gamma_abc_g1_iter.next().cloned().unwrap();
            for (i, (input, b)) in public_inputs.val.iter().zip(gamma_abc_g1_iter).enumerate() {
                g_ic = b.mul_bits(cs.ns(|| format!("Mul {}", i)), &g_ic, input.into_iter().copied())?;
            }
            g_ic
        };

        let test_exp = {
            let proof_a_prep = P::prepare_g1(cs.ns(|| "Prepare proof a"), proof.a.clone())?;
            let proof_b_prep = P::prepare_g2(cs.ns(|| "Prepare proof b"), proof.b.clone())?;
            let proof_c_prep = P::prepare_g1(cs.ns(|| "Prepare proof c"), proof.c.clone())?;

            let g_ic_prep = P::prepare_g1(cs.ns(|| "Prepare g_ic"), g_ic)?;

            P::miller_loop(cs.ns(|| "Miller loop 1"), &[proof_a_prep, g_ic_prep, proof_c_prep], &[
                proof_b_prep,
                gamma_g2_neg_pc,
                delta_g2_neg_pc,
            ])?
        };

        let test = P::final_exponentiation(cs.ns(|| "Final Exp"), &test_exp).unwrap();

        test.enforce_equal(cs.ns(|| "Test 1"), &alpha_g1_beta_g2)?;
        Ok(())
    }
}

impl<PairingE, P> ToConstraintFieldGadget<PairingE::Fq> for VerifyingKeyGadget<PairingE, P>
where
    PairingE: PairingEngine,
    P: PairingGadget<PairingE>,
{
    fn to_constraint_field<CS: ConstraintSystem<PairingE::Fq>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<FpGadget<PairingE::Fq>>, SynthesisError> {
        let mut res = Vec::new();
        res.append(&mut self.alpha_g1.to_constraint_field(cs.ns(|| "alpha_g1"))?);
        res.append(&mut self.beta_g2.to_constraint_field(cs.ns(|| "beta_g2"))?);
        res.append(&mut self.gamma_g2.to_constraint_field(cs.ns(|| "gamma_g2"))?);
        res.append(&mut self.delta_g2.to_constraint_field(cs.ns(|| "delta_g2"))?);
        for (i, query_elem) in self.gamma_abc_g1.iter().enumerate() {
            res.append(&mut query_elem.to_constraint_field(cs.ns(|| format!("query_{}", i)))?);
        }

        Ok(res)
    }
}

impl<PairingE, P> AllocGadget<VerifyingKey<PairingE>, PairingE::Fq> for VerifyingKeyGadget<PairingE, P>
where
    PairingE: PairingEngine,
    P: PairingGadget<PairingE, PairingE::Fq>,
{
    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<PairingE::Fq>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifyingKey<PairingE>>,
    {
        value_gen().and_then(|vk| {
            let VerifyingKey {
                alpha_g1,
                beta_g2,
                gamma_g2,
                delta_g2,
                gamma_abc_g1,
            } = vk.borrow();
            let alpha_g1 = P::G1Gadget::alloc(cs.ns(|| "alpha_g1"), || Ok(alpha_g1.into_projective()))?;
            let beta_g2 = P::G2Gadget::alloc(cs.ns(|| "beta_g2"), || Ok(beta_g2.into_projective()))?;
            let gamma_g2 = P::G2Gadget::alloc(cs.ns(|| "gamma_g2"), || Ok(gamma_g2.into_projective()))?;
            let delta_g2 = P::G2Gadget::alloc(cs.ns(|| "delta_g2"), || Ok(delta_g2.into_projective()))?;

            let gamma_abc_g1 = gamma_abc_g1
                .iter()
                .enumerate()
                .map(|(i, gamma_abc_i)| {
                    P::G1Gadget::alloc(cs.ns(|| format!("gamma_abc_{}", i)), || {
                        Ok(gamma_abc_i.into_projective())
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Self {
                alpha_g1,
                beta_g2,
                gamma_g2,
                delta_g2,
                gamma_abc_g1,
            })
        })
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<PairingE::Fq>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifyingKey<PairingE>>,
    {
        value_gen().and_then(|vk| {
            let VerifyingKey {
                alpha_g1,
                beta_g2,
                gamma_g2,
                delta_g2,
                gamma_abc_g1,
            } = vk.borrow();
            let alpha_g1 = P::G1Gadget::alloc_input(cs.ns(|| "alpha_g1"), || Ok(alpha_g1.into_projective()))?;
            let beta_g2 = P::G2Gadget::alloc_input(cs.ns(|| "beta_g2"), || Ok(beta_g2.into_projective()))?;
            let gamma_g2 = P::G2Gadget::alloc_input(cs.ns(|| "gamma_g2"), || Ok(gamma_g2.into_projective()))?;
            let delta_g2 = P::G2Gadget::alloc_input(cs.ns(|| "delta_g2"), || Ok(delta_g2.into_projective()))?;

            let gamma_abc_g1 = gamma_abc_g1
                .iter()
                .enumerate()
                .map(|(i, gamma_abc_i)| {
                    P::G1Gadget::alloc_input(cs.ns(|| format!("gamma_abc_{}", i)), || {
                        Ok(gamma_abc_i.into_projective())
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;

            Ok(Self {
                alpha_g1,
                beta_g2,
                gamma_g2,
                delta_g2,
                gamma_abc_g1,
            })
        })
    }
}

impl<PairingE, P> AllocBytesGadget<Vec<u8>, PairingE::Fq> for VerifyingKeyGadget<PairingE, P>
where
    PairingE: PairingEngine,
    P: PairingGadget<PairingE>,
{
    #[inline]
    fn alloc_bytes<FN, T, CS: ConstraintSystem<PairingE::Fq>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Vec<u8>>,
    {
        value_gen().and_then(|vk_bytes| {
            let vk: VerifyingKey<PairingE> = FromBytes::read_le(&vk_bytes.borrow()[..])?;

            Self::alloc(cs.ns(|| "alloc_bytes"), || Ok(vk))
        })
    }

    #[inline]
    fn alloc_input_bytes<FN, T, CS: ConstraintSystem<PairingE::Fq>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Vec<u8>>,
    {
        value_gen().and_then(|vk_bytes| {
            let vk: VerifyingKey<PairingE> = FromBytes::read_le(&vk_bytes.borrow()[..])?;

            Self::alloc_input(cs.ns(|| "alloc_input_bytes"), || Ok(vk))
        })
    }
}

impl<PairingE, P> AllocGadget<Proof<PairingE>, PairingE::Fq> for ProofGadget<PairingE, P>
where
    PairingE: PairingEngine,
    P: PairingGadget<PairingE>,
{
    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<PairingE::Fq>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<PairingE>>,
    {
        value_gen().and_then(|proof| {
            let Proof { a, b, c, .. } = proof.borrow();
            let a = P::G1Gadget::alloc_checked(cs.ns(|| "a"), || Ok(a.into_projective()))?;
            let b = P::G2Gadget::alloc_checked(cs.ns(|| "b"), || Ok(b.into_projective()))?;
            let c = P::G1Gadget::alloc_checked(cs.ns(|| "c"), || Ok(c.into_projective()))?;
            Ok(Self { a, b, c })
        })
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<PairingE::Fq>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<PairingE>>,
    {
        value_gen().and_then(|proof| {
            let Proof { a, b, c, .. } = proof.borrow();
            // We don't need to check here because the prime order check can be performed
            // in plain.
            let a = P::G1Gadget::alloc_input(cs.ns(|| "a"), || Ok(a.into_projective()))?;
            let b = P::G2Gadget::alloc_input(cs.ns(|| "b"), || Ok(b.into_projective()))?;
            let c = P::G1Gadget::alloc_input(cs.ns(|| "c"), || Ok(c.into_projective()))?;
            Ok(Self { a, b, c })
        })
    }
}

impl<PairingE, P> AllocBytesGadget<Vec<u8>, PairingE::Fq> for ProofGadget<PairingE, P>
where
    PairingE: PairingEngine,
    P: PairingGadget<PairingE, PairingE::Fq>,
{
    #[inline]
    fn alloc_bytes<FN, T, CS: ConstraintSystem<PairingE::Fq>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Vec<u8>>,
    {
        value_gen().and_then(|proof_bytes| {
            let proof: Proof<PairingE> = FromBytes::read_le(&proof_bytes.borrow()[..])?;

            Self::alloc(cs.ns(|| "alloc_bytes"), || Ok(proof))
        })
    }

    #[inline]
    fn alloc_input_bytes<FN, T, CS: ConstraintSystem<PairingE::Fq>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Vec<u8>>,
    {
        value_gen().and_then(|proof_bytes| {
            let proof: Proof<PairingE> = FromBytes::read_le(&proof_bytes.borrow()[..])?;

            Self::alloc_input(cs.ns(|| "alloc_input_bytes"), || Ok(proof))
        })
    }
}

impl<PairingE, P> ToBytesGadget<PairingE::Fq> for VerifyingKeyGadget<PairingE, P>
where
    PairingE: PairingEngine,
    P: PairingGadget<PairingE>,
{
    #[inline]
    fn to_bytes<CS: ConstraintSystem<PairingE::Fq>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&self.alpha_g1.to_bytes(&mut cs.ns(|| "alpha_g1 to bytes"))?);
        bytes.extend_from_slice(&self.beta_g2.to_bytes(&mut cs.ns(|| "beta_g2 to bytes"))?);
        bytes.extend_from_slice(&self.gamma_g2.to_bytes(&mut cs.ns(|| "gamma_g2 to bytes"))?);
        bytes.extend_from_slice(&self.delta_g2.to_bytes(&mut cs.ns(|| "delta_g2 to bytes"))?);
        bytes.extend_from_slice(&UInt8::alloc_vec(
            &mut cs.ns(|| "gamma_abc_g1_length"),
            &(self.gamma_abc_g1.len() as u32).to_le_bytes()[..],
        )?);
        for (i, g) in self.gamma_abc_g1.iter().enumerate() {
            let mut cs = cs.ns(|| format!("Iteration {}", i));
            bytes.extend_from_slice(&g.to_bytes(&mut cs.ns(|| "g"))?);
        }
        Ok(bytes)
    }

    #[inline]
    fn to_bytes_strict<CS: ConstraintSystem<PairingE::Fq>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&self.alpha_g1.to_bytes_strict(&mut cs.ns(|| "alpha_g1 to bytes"))?);
        bytes.extend_from_slice(&self.beta_g2.to_bytes_strict(&mut cs.ns(|| "beta_g2 to bytes"))?);
        bytes.extend_from_slice(&self.gamma_g2.to_bytes_strict(&mut cs.ns(|| "gamma_g2 to bytes"))?);
        bytes.extend_from_slice(&self.delta_g2.to_bytes_strict(&mut cs.ns(|| "delta_g2 to bytes"))?);
        bytes.extend_from_slice(&UInt8::alloc_vec(
            &mut cs.ns(|| "gamma_abc_g1_length"),
            &(self.gamma_abc_g1.len() as u32).to_le_bytes()[..],
        )?);
        for (i, g) in self.gamma_abc_g1.iter().enumerate() {
            let mut cs = cs.ns(|| format!("Iteration {}", i));
            bytes.extend_from_slice(&g.to_bytes_strict(&mut cs.ns(|| "g"))?);
        }
        Ok(bytes)
    }
}
