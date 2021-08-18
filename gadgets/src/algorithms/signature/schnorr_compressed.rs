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
    bits::{Boolean, ToBytesGadget},
    integers::uint::UInt8,
    traits::{
        algorithms::SignatureGadget,
        alloc::AllocGadget,
        curves::GroupGadget,
        eq::{ConditionalEqGadget, EqGadget},
        integers::Integer,
        select::CondSelectGadget,
    },
    CryptoHashGadget,
    FpGadget,
    ToBitsLEGadget,
    ToConstraintFieldGadget,
};
use snarkvm_algorithms::{
    crypto_hash::PoseidonDefaultParametersField,
    signature::{SchnorrCompressed, SchnorrCompressedPublicKey, SchnorrCompressedSignature},
};
use snarkvm_curves::{templates::twisted_edwards_extended::Affine as TEAffine, TwistedEdwardsParameters};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use crate::algorithms::crypto_hash::PoseidonCryptoHashGadget;
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
pub struct SchnorrCompressedPublicKeyGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField>(
    TEAffineGadget<TE, F>,
);

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<SchnorrCompressedPublicKey<TE>, F>
    for SchnorrCompressedPublicKeyGadget<TE, F>
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrCompressedPublicKey<TE>>,
        CS: ConstraintSystem<F>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            0: TEAffineGadget::<TE, F>::alloc_constant(cs, || Ok(value_gen()?.borrow().0.clone()))?,
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrCompressedPublicKey<TE>>,
        CS: ConstraintSystem<F>,
    >(
        cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            0: TEAffineGadget::<TE, F>::alloc_checked(cs, || Ok(value_gen()?.borrow().0.clone()))?,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrCompressedPublicKey<TE>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let point = if let Ok(pk) = value_gen() {
            pk.borrow().0.clone()
        } else {
            TEAffine::<TE>::default()
        };

        let x_coordinate_gadget =
            FpGadget::<TE::BaseField>::alloc_input(cs.ns(|| "input x coordinate"), || Ok(point.x))?;
        let allocated_gadget =
            TEAffineGadget::<TE, F>::alloc_checked(cs.ns(|| "input the allocated point"), || Ok(point.clone()))?;

        allocated_gadget
            .x
            .enforce_equal(cs.ns(|| "check x consistency"), &x_coordinate_gadget)?;

        Ok(Self { 0: allocated_gadget })
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ConditionalEqGadget<F>
    for SchnorrCompressedPublicKeyGadget<TE, F>
{
    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.0
            .conditional_enforce_equal(&mut cs.ns(|| "conditional_enforce_equal"), &other.0, condition)?;
        Ok(())
    }

    fn cost() -> usize {
        <TEAffineGadget<TE, F> as ConditionalEqGadget<F>>::cost()
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> EqGadget<F>
    for SchnorrCompressedPublicKeyGadget<TE, F>
{
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ToBytesGadget<F>
    for SchnorrCompressedPublicKeyGadget<TE, F>
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
pub struct SchnorrCompressedSignatureGadget<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> {
    pub(crate) prover_response: FpGadget<F>,
    pub(crate) verifier_challenge: FpGadget<F>,
    pub(crate) _group: PhantomData<TE>,
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> AllocGadget<SchnorrCompressedSignature<TE>, F>
    for SchnorrCompressedSignatureGadget<TE, F>
{
    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrCompressedSignature<TE>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let schnorr_output = value.borrow().clone();

        // TODO (raychu86): Check that this conversion is valid.
        //      This will work for EdwardsBls Fr and Bls12_377 Fr because they are both represented with Fp256.

        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read_le(&to_bytes_le![schnorr_output.prover_response]?[..])?;
        let verifier_challenge: F = FromBytes::read_le(&to_bytes_le![schnorr_output.verifier_challenge]?[..])?;

        let prover_response = FpGadget::<F>::alloc(cs.ns(|| "alloc_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FpGadget::<F>::alloc(cs.ns(|| "alloc_verifier_challenge"), || Ok(&verifier_challenge))?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            _group: PhantomData,
        })
    }

    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrCompressedSignature<TE>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let schnorr_output = value.borrow().clone();

        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read_le(&to_bytes_le![schnorr_output.prover_response]?[..])?;
        let verifier_challenge: F = FromBytes::read_le(&to_bytes_le![schnorr_output.verifier_challenge]?[..])?;

        let prover_response =
            FpGadget::<F>::alloc_constant(cs.ns(|| "alloc_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FpGadget::<F>::alloc_constant(cs.ns(|| "alloc_verifier_challenge"), || Ok(&verifier_challenge))?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            _group: PhantomData,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrCompressedSignature<TE>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let schnorr_output = value.borrow().clone();

        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read_le(&to_bytes_le![schnorr_output.prover_response]?[..])?;
        let verifier_challenge: F = FromBytes::read_le(&to_bytes_le![schnorr_output.verifier_challenge]?[..])?;

        let prover_response =
            FpGadget::<F>::alloc_input(cs.ns(|| "alloc_input_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FpGadget::<F>::alloc_input(cs.ns(|| "alloc_input_verifier_challenge"), || Ok(&verifier_challenge))?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            _group: PhantomData,
        })
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ConditionalEqGadget<F>
    for SchnorrCompressedSignatureGadget<TE, F>
{
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
        Ok(())
    }

    fn cost() -> usize {
        <FpGadget<F> as ConditionalEqGadget<F>>::cost() * 2
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> EqGadget<F>
    for SchnorrCompressedSignatureGadget<TE, F>
{
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField> ToBytesGadget<F>
    for SchnorrCompressedSignatureGadget<TE, F>
{
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut result = Vec::new();

        result.extend(
            self.prover_response
                .to_bytes(&mut cs.ns(|| "prover_response_to_bytes"))?,
        );
        result.extend(
            self.verifier_challenge
                .to_bytes(&mut cs.ns(|| "verifier_challenge_to_bytes"))?,
        );

        Ok(result)
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut result = Vec::new();

        result.extend(
            self.prover_response
                .to_bytes_strict(&mut cs.ns(|| "prover_response_to_bytes_strict"))?,
        );
        result.extend(
            self.verifier_challenge
                .to_bytes_strict(&mut cs.ns(|| "verifier_challenge_to_bytes_strict"))?,
        );

        Ok(result)
    }
}

pub struct SchnorrCompressedGadget<
    TE: TwistedEdwardsParameters<BaseField = F>,
    F: PrimeField + PoseidonDefaultParametersField,
> {
    pub(crate) signature: SchnorrCompressed<TE>,
    pub(crate) _engine: PhantomData<F>,
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField + PoseidonDefaultParametersField>
    AllocGadget<SchnorrCompressed<TE>, F> for SchnorrCompressedGadget<TE, F>
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrCompressed<TE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            signature: (*value_gen()?.borrow()).clone(),
            _engine: PhantomData,
        })
    }

    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<SchnorrCompressed<TE>>, CS: ConstraintSystem<F>>(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrCompressed<TE>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        _value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        unimplemented!()
    }
}

impl<TE: TwistedEdwardsParameters<BaseField = F>, F: PrimeField + PoseidonDefaultParametersField>
    SignatureGadget<SchnorrCompressed<TE>, F> for SchnorrCompressedGadget<TE, F>
{
    type PublicKeyGadget = SchnorrCompressedPublicKeyGadget<TE, F>;
    type SignatureGadget = SchnorrCompressedSignatureGadget<TE, F>;

    fn randomize_public_key<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        public_key: &Self::PublicKeyGadget,
        randomizer: &[UInt8],
    ) -> Result<Self::PublicKeyGadget, SynthesisError> {
        let affine_zero: TEAffineGadget<TE, F> =
            <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::zero(cs.ns(|| "affine zero")).unwrap();

        let randomness = randomizer.iter().flat_map(|b| b.to_bits_le()).collect::<Vec<_>>();

        let mut randomized_public_key = affine_zero;
        randomized_public_key.scalar_multiplication(
            cs.ns(|| "check_randomization_gadget"),
            randomness.iter().zip_eq(&self.signature.generator_powers),
        )?;
        randomized_public_key = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::add(
            &randomized_public_key,
            cs.ns(|| "pk + rG"),
            &public_key.0,
        )?;

        Ok(SchnorrCompressedPublicKeyGadget {
            0: randomized_public_key,
        })
    }

    fn verify<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        public_key: &Self::PublicKeyGadget,
        message: &[UInt8],
        signature: &Self::SignatureGadget,
    ) -> Result<Boolean, SynthesisError> {
        let affine_zero: TEAffineGadget<TE, F> =
            <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::zero(cs.ns(|| "affine zero")).unwrap();

        let prover_response_bytes = signature
            .prover_response
            .to_bytes(cs.ns(|| "prover_response_to_bytes"))?;

        let prover_response_bits = prover_response_bytes.iter().flat_map(|byte| byte.to_bits_le());
        let verifier_challenge_bits = signature
            .verifier_challenge
            .to_bits_le(cs.ns(|| "verifier_challenge_to_bits"))?;

        let mut claimed_prover_commitment = affine_zero.clone();
        for (i, (bit, base_power)) in prover_response_bits
            .zip_eq(&self.signature.generator_powers)
            .enumerate()
        {
            let added =
                claimed_prover_commitment.add_constant(cs.ns(|| format!("add_base_power_{}", i)), base_power)?;

            claimed_prover_commitment = TEAffineGadget::<TE, F>::conditionally_select(
                cs.ns(|| format!("cond_select_{}", i)),
                &bit,
                &added,
                &claimed_prover_commitment,
            )?;
        }

        let public_key_times_verifier_challenge = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::mul_bits(
            &public_key.0,
            cs.ns(|| "record_view_key"),
            &affine_zero,
            verifier_challenge_bits.into_iter(),
        )?;

        claimed_prover_commitment = <TEAffineGadget<TE, F> as GroupGadget<TEAffine<TE>, F>>::add(
            &claimed_prover_commitment,
            cs.ns(|| "claimed_prover_commitment_plus_public_key_times_verifier_challenge"),
            &public_key_times_verifier_challenge,
        )?;

        // Construct the hash
        let mut hash_input = Vec::new();
        hash_input.extend_from_slice(
            &claimed_prover_commitment
                .x
                .to_constraint_field(cs.ns(|| "convert claimed_prover_commitment into field elements"))?,
        );
        hash_input.extend_from_slice(
            &public_key
                .0
                .x
                .to_constraint_field(cs.ns(|| "convert public key into field elements"))?,
        );
        hash_input.push(FpGadget::<F>::Constant(F::from(message.len() as u128)));
        hash_input.extend_from_slice(&message.to_constraint_field(cs.ns(|| "convert message into field elements"))?);

        // Compute the hash on the base field
        let raw_hash =
            PoseidonCryptoHashGadget::<F, 4, false>::check_evaluation_gadget(cs.ns(|| "poseidon"), &hash_input)?;

        // Bit decompose the raw_hash
        let mut raw_hash_bits = raw_hash.to_bits_le(cs.ns(|| "convert the hash into bits"))?;
        raw_hash_bits.resize(
            <TE::ScalarField as PrimeField>::Parameters::CAPACITY as usize,
            Boolean::Constant(false),
        );

        let hash = Boolean::le_bits_to_fp_var(cs.ns(|| "obtain the truncated hash"), &raw_hash_bits)?;
        let result = signature
            .verifier_challenge
            .is_eq(cs.ns(|| "check verifier challenge"), &hash)?;

        Ok(result)
    }
}
