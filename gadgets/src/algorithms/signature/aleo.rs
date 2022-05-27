// Copyright (C) 2019-2022 Aleo Systems Inc.
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
    algorithms::crypto_hash::PoseidonCryptoHashGadget,
    bits::{Boolean, ToBytesGadget},
    integers::uint::UInt8,
    traits::{
        algorithms::SignatureGadget,
        alloc::AllocGadget,
        curves::GroupGadget,
        eq::{ConditionalEqGadget, EqGadget},
        select::CondSelectGadget,
    },
    CompressedGroupGadget,
    FpGadget,
    ToBitsLEGadget,
    ToConstraintFieldGadget,
};
use snarkvm_algorithms::{
    signature::{AleoSignature, AleoSignatureScheme},
    SignatureScheme,
};
use snarkvm_curves::{
    templates::twisted_edwards_extended::Affine as TEAffine,
    ProjectiveCurve,
    TwistedEdwardsParameters,
};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use itertools::Itertools;
use std::{borrow::Borrow, marker::PhantomData};

type TEAffineGadget<TE, F> = crate::curves::templates::twisted_edwards::AffineGadget<TE, F, FpGadget<F>>;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    PartialEq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Eq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Debug(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField")
)]
pub struct AleoSignaturePublicKeyGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField>(
    pub TEAffineGadget<TE, F>,
);

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<TEAffine<TE>, F>
    for AleoSignaturePublicKeyGadget<TE, F>
{
    fn alloc_constant<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TEAffine<TE>>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let public_key = *value_gen()?.borrow();
        Ok(Self(TEAffineGadget::<TE, F>::alloc_constant(cs, || Ok(public_key))?))
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TEAffine<TE>>, CS: ConstraintSystem<F>>(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let public_key = *value_gen()?.borrow();
        Ok(Self(TEAffineGadget::<TE, F>::alloc_checked(cs, || Ok(public_key))?))
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<TEAffine<TE>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let point = if let Ok(pk) = value_gen() { *pk.borrow() } else { TEAffine::<TE>::default() };

        let x_coordinate_gadget =
            FpGadget::<TE::BaseField>::alloc_input(cs.ns(|| "input x coordinate"), || Ok(point.x))?;
        let allocated_gadget =
            TEAffineGadget::<TE, F>::alloc_checked(cs.ns(|| "input the allocated point"), || Ok(point))?;

        allocated_gadget.x.enforce_equal(cs.ns(|| "check x consistency"), &x_coordinate_gadget)?;

        Ok(Self(allocated_gadget))
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ConditionalEqGadget<F>
    for AleoSignaturePublicKeyGadget<TE, F>
{
    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.0.conditional_enforce_equal(&mut cs.ns(|| "conditional_enforce_equal"), &other.0, condition)?;
        Ok(())
    }

    fn cost() -> usize {
        <TEAffineGadget<TE, F> as ConditionalEqGadget<F>>::cost()
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> EqGadget<F> for AleoSignaturePublicKeyGadget<TE, F> {
    fn is_eq<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        self.0.is_eq(&mut cs.ns(|| "is_eq"), &other.0)
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ToBytesGadget<F>
    for AleoSignaturePublicKeyGadget<TE, F>
{
    fn to_bytes<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.x.to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.0.x.to_bytes_strict(cs)
    }
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    PartialEq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Eq(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField"),
    Debug(bound = "TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField")
)]
pub struct AleoSignatureGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> {
    pub(crate) prover_response: FpGadget<F>,
    pub(crate) verifier_challenge: FpGadget<F>,
    pub(crate) root_public_key: TEAffineGadget<TE, F>,
    pub(crate) root_randomizer: TEAffineGadget<TE, F>,
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<AleoSignature<TE>, F>
    for AleoSignatureGadget<TE, F>
{
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<AleoSignature<TE>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let signature = *value.borrow();

        // TODO (raychu86): Check that this conversion is valid.
        //      This will work for EdwardsBls Fr and Bls12_377 Fr because they are both represented with Fp256.

        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read_le(&signature.prover_response.to_bytes_le()?[..])?;
        let verifier_challenge: F = FromBytes::read_le(&signature.verifier_challenge.to_bytes_le()?[..])?;

        let prover_response = FpGadget::<F>::alloc(cs.ns(|| "alloc_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FpGadget::<F>::alloc(cs.ns(|| "alloc_verifier_challenge"), || Ok(&verifier_challenge))?;
        let root_public_key =
            TEAffineGadget::<TE, F>::alloc(cs.ns(|| "alloc_root_public_key"), || Ok(signature.root_public_key()?))?;
        let root_randomizer =
            TEAffineGadget::<TE, F>::alloc(cs.ns(|| "alloc_root_randomizer"), || Ok(signature.root_randomizer()?))?;

        Ok(Self { prover_response, verifier_challenge, root_public_key, root_randomizer })
    }

    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<AleoSignature<TE>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let signature = *value.borrow();

        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read_le(&signature.prover_response.to_bytes_le()?[..])?;
        let verifier_challenge: F = FromBytes::read_le(&signature.verifier_challenge.to_bytes_le()?[..])?;

        let prover_response =
            FpGadget::<F>::alloc_constant(cs.ns(|| "alloc_constant_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FpGadget::<F>::alloc_constant(cs.ns(|| "alloc_constant_verifier_challenge"), || Ok(&verifier_challenge))?;
        let root_public_key =
            TEAffineGadget::<TE, F>::alloc_constant(cs.ns(|| "alloc_constant_root_public_key"), || {
                Ok(signature.root_public_key()?)
            })?;
        let root_randomizer =
            TEAffineGadget::<TE, F>::alloc_constant(cs.ns(|| "alloc_constant_root_randomizer"), || {
                Ok(signature.root_randomizer()?)
            })?;

        Ok(Self { prover_response, verifier_challenge, root_public_key, root_randomizer })
    }

    fn alloc_input<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<AleoSignature<TE>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let signature = *value.borrow();

        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read_le(&signature.prover_response.to_bytes_le()?[..])?;
        let verifier_challenge: F = FromBytes::read_le(&signature.verifier_challenge.to_bytes_le()?[..])?;

        let prover_response =
            FpGadget::<F>::alloc_input(cs.ns(|| "alloc_input_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FpGadget::<F>::alloc_input(cs.ns(|| "alloc_input_verifier_challenge"), || Ok(&verifier_challenge))?;
        let root_public_key = TEAffineGadget::<TE, F>::alloc_input(cs.ns(|| "alloc_input_root_public_key"), || {
            Ok(signature.root_public_key()?)
        })?;
        let root_randomizer = TEAffineGadget::<TE, F>::alloc_input(cs.ns(|| "alloc_input_root_randomizer"), || {
            Ok(signature.root_randomizer()?)
        })?;

        Ok(Self { prover_response, verifier_challenge, root_public_key, root_randomizer })
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ConditionalEqGadget<F> for AleoSignatureGadget<TE, F> {
    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.prover_response.conditional_enforce_equal(
            &mut cs.ns(|| "prover_response_conditional_enforce_equal"),
            &other.prover_response,
            condition,
        )?;
        self.verifier_challenge.conditional_enforce_equal(
            &mut cs.ns(|| "verifier_challenge_conditional_enforce_equal"),
            &other.verifier_challenge,
            condition,
        )?;
        self.root_public_key.conditional_enforce_equal(
            &mut cs.ns(|| "root_public_key_conditional_enforce_equal"),
            &other.root_public_key,
            condition,
        )?;
        self.root_randomizer.conditional_enforce_equal(
            &mut cs.ns(|| "root_randomizer_conditional_enforce_equal"),
            &other.root_randomizer,
            condition,
        )?;
        Ok(())
    }

    fn cost() -> usize {
        <FpGadget<F> as ConditionalEqGadget<F>>::cost() * 2
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> EqGadget<F> for AleoSignatureGadget<TE, F> {}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ToBytesGadget<F> for AleoSignatureGadget<TE, F> {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut result = Vec::new();

        result.extend(self.prover_response.to_bytes(&mut cs.ns(|| "prover_response_to_bytes"))?);
        result.extend(self.verifier_challenge.to_bytes(&mut cs.ns(|| "verifier_challenge_to_bytes"))?);
        result.extend(self.root_public_key.to_bytes(&mut cs.ns(|| "root_public_key_to_bytes"))?);
        result.extend(self.root_randomizer.to_bytes(&mut cs.ns(|| "root_randomizer_to_bytes"))?);

        Ok(result)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut result = Vec::new();

        result.extend(self.prover_response.to_bytes_strict(&mut cs.ns(|| "prover_response_to_bytes_strict"))?);
        result.extend(self.verifier_challenge.to_bytes_strict(&mut cs.ns(|| "verifier_challenge_to_bytes_strict"))?);
        result.extend(self.root_public_key.to_bytes_strict(&mut cs.ns(|| "root_public_key_to_bytes_strict"))?);
        result.extend(self.root_randomizer.to_bytes_strict(&mut cs.ns(|| "root_randomizer_to_bytes_strict"))?);

        Ok(result)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AleoComputeKeyGadget {
    /// We only include `sk_prf`, and not `root_public_key` or `root_randomizer`,
    /// as this is all we need in the circuit.
    pub(crate) sk_prf_bits: Vec<Boolean>,
}

impl<F: PrimeField> ToBitsLEGadget<F> for AleoComputeKeyGadget {
    fn to_bits_le<CS: ConstraintSystem<F>>(&self, _cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.sk_prf_bits.to_vec())
    }

    fn to_bits_le_strict<CS: ConstraintSystem<F>>(&self, cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        self.to_bits_le(cs)
    }
}

pub struct AleoSignatureSchemeGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> {
    pub(crate) signature: AleoSignatureScheme<TE>,
    pub(crate) _engine: PhantomData<F>,
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<AleoSignatureScheme<TE>, F>
    for AleoSignatureSchemeGadget<TE, F>
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<AleoSignatureScheme<TE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self { signature: (*value_gen()?.borrow()).clone(), _engine: PhantomData })
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<AleoSignatureScheme<TE>>, CS: ConstraintSystem<F>>(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<AleoSignatureScheme<TE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> SignatureGadget<AleoSignatureScheme<TE>, F>
    for AleoSignatureSchemeGadget<TE, F>
{
    type ComputeKeyGadget = AleoComputeKeyGadget;
    type PublicKeyGadget = AleoSignaturePublicKeyGadget<TE, F>;
    type SignatureGadget = AleoSignatureGadget<TE, F>;

    fn compute_key<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        signature: &Self::SignatureGadget,
    ) -> Result<Self::ComputeKeyGadget, SynthesisError> {
        let output = PoseidonCryptoHashGadget::<F, 4>::check_evaluation_gadget(
            &mut cs.ns(|| "Hash root_public_key and root_randomizer"),
            &[signature.root_public_key.to_x_coordinate(), signature.root_randomizer.to_x_coordinate()],
        )?;

        // Truncate the output to CAPACITY bits (1 bit less than MODULUS_BITS) in the scalar field.
        let mut sk_prf_bits = output.to_bits_le_strict(&mut cs.ns(|| "Output hash to bytes"))?;
        sk_prf_bits.resize(TE::ScalarField::size_in_data_bits(), Boolean::Constant(false));
        Ok(AleoComputeKeyGadget { sk_prf_bits })
    }

    fn verify<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        public_key: &Self::PublicKeyGadget,
        message: &[Boolean],
        signature: &Self::SignatureGadget,
    ) -> Result<Boolean, SynthesisError> {
        // Prepare the zero element in affine form for use.
        let zero_affine: TEAffineGadget<TE, F> =
            <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::zero(cs.ns(|| "affine zero"))?;

        // Prepare s, by converting the prover response to bits.
        let s = {
            let mut s_bits =
                signature.prover_response.to_bits_le_strict(cs.ns(|| "prover_response to_bits_le_strict"))?;

            // Truncate s to fit the scalar field.
            s_bits.resize(<TE::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize, Boolean::Constant(false));
            s_bits
        };

        // Compute G^s.
        let g_s = {
            let mut g_s = zero_affine.clone();
            for (i, (base, bit)) in self.signature.parameters().iter().zip_eq(s).enumerate() {
                let added = g_s.add_constant(cs.ns(|| format!("add_g_s_{}", i)), &base.to_affine())?;

                g_s = TEAffineGadget::<TE, F>::conditionally_select(
                    cs.ns(|| format!("cond_select_g_s_{}", i)),
                    &bit,
                    &added,
                    &g_s,
                )?;
            }
            g_s
        };

        // Prepare c, by converting the verifier challenge to bits.
        let c = {
            let mut c_bits =
                signature.verifier_challenge.to_bits_le_strict(cs.ns(|| "verifier_challenge to_bits_le_strict"))?;

            // Truncate c to fit the scalar field.
            c_bits.resize(<TE::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize, Boolean::Constant(false));
            c_bits
        };

        // Extract G^sk_sig.
        let g_sk_sig = &signature.root_public_key;

        // Compute G^sk_sig^c.
        let g_sk_sig_c = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::mul_bits(
            g_sk_sig,
            cs.ns(|| "G^sk_sig^c"),
            &zero_affine,
            c.into_iter(),
        )?;

        // Compute G^r := G^s G^sk_sig^c.
        let g_r = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::add(
            &g_s,
            cs.ns(|| "G^r := G^s G^sk_sig^c"),
            &g_sk_sig_c,
        )?;

        // Compute the candidate verifier challenge.
        let candidate_verifier_challenge = {
            // Construct the hash input (G^sk_sig G^r_sig G^sk_prf, G^r, message).
            let mut preimage = Vec::new();
            preimage
                .extend_from_slice(&public_key.0.x.to_constraint_field(cs.ns(|| "public_key to constraint field"))?);
            preimage.extend_from_slice(&g_r.x.to_constraint_field(cs.ns(|| "G^r to constraint field"))?);
            preimage.push(FpGadget::<F>::Constant(F::from(message.len() as u128)));
            preimage.extend_from_slice(&message.to_constraint_field(cs.ns(|| "convert message into field elements"))?);

            // Compute the hash of the preimage on the base field.
            let hash =
                PoseidonCryptoHashGadget::<F, 4>::check_evaluation_gadget(cs.ns(|| "Poseidon of preimage"), &preimage)?;

            // Truncate the output to fit the scalar field.
            let mut hash_bits = hash.to_bits_le(cs.ns(|| "convert the hash into bits"))?;
            hash_bits.resize(<TE::ScalarField as PrimeField>::Parameters::CAPACITY as usize, Boolean::Constant(false));

            // Output the verifier challenge.
            Boolean::le_bits_to_fp_var(cs.ns(|| "obtain the truncated hash"), &hash_bits)?
        };

        // Extract G^r_sig.
        let g_r_sig = &signature.root_randomizer;

        // Compute the candidate public key as (G^sk_sig G^r_sig G^sk_prf).
        let candidate_public_key = {
            // Compute sk_prf := RO(G^sk_sig || G^r_sig).
            let sk_prf = {
                // Compute the hash of (G^sk_sig || G^r_sig) on the base field.
                let output = PoseidonCryptoHashGadget::<F, 4>::check_evaluation_gadget(
                    cs.ns(|| "Poseidon(G^sk_sig || G^r_sig)"),
                    &[g_sk_sig.x.clone(), g_r_sig.x.clone()],
                )?;

                // Truncate the output to fit the scalar field.
                let mut sk_prf_bits = output.to_bits_le(cs.ns(|| "Convert the output into bits"))?;
                sk_prf_bits
                    .resize(<TE::ScalarField as PrimeField>::Parameters::CAPACITY as usize, Boolean::Constant(false));
                sk_prf_bits.push(Boolean::Constant(false)); // Append one 0 bit to match MODULUS_BITS size.
                sk_prf_bits
            };

            // Compute G^sk_prf.
            let g_sk_prf = {
                let mut g_sk_prf = zero_affine;
                for (i, (base, bit)) in self.signature.parameters().iter().zip_eq(sk_prf).enumerate() {
                    let added = g_sk_prf.add_constant(cs.ns(|| format!("add_g_sk_prf_{}", i)), &base.to_affine())?;

                    g_sk_prf = TEAffineGadget::<TE, F>::conditionally_select(
                        cs.ns(|| format!("cond_select_g_sk_prf_{}", i)),
                        &bit,
                        &added,
                        &g_sk_prf,
                    )?;
                }
                g_sk_prf
            };

            // Compute G^sk_sig G^r_sig.
            let g_sk_sig_g_r_sig = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::add(
                g_sk_sig,
                cs.ns(|| "G^sk_sig G^r_sig"),
                g_r_sig,
            )?;

            // Compute G^sk_sig G^r_sig G^sk_prf.
            <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::add(
                &g_sk_sig_g_r_sig,
                cs.ns(|| "G^sk_sig G^r_sig G^sk_prf"),
                &g_sk_prf,
            )?
        };

        // Check the verifier challenge equals.
        let verifier_challenge_equals =
            signature.verifier_challenge.is_eq(cs.ns(|| "Check verifier challenge"), &candidate_verifier_challenge)?;

        // Check the public key equals.
        let public_key_equals = public_key.0.is_eq(cs.ns(|| "Check public key"), &candidate_public_key)?;

        Boolean::and(cs.ns(|| "a ^ b"), &verifier_challenge_equals, &public_key_equals)
    }
}
