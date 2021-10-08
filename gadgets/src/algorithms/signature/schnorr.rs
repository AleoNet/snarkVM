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
    bits::{Boolean, ToBytesLEGadget},
    integers::uint::UInt8,
    traits::{
        algorithms::SignaturePublicKeyRandomizationGadget,
        alloc::AllocGadget,
        curves::GroupGadget,
        eq::{ConditionalEqGadget, EqGadget},
    },
    FieldGadget,
    PRFGadget,
};
use snarkvm_algorithms::{
    prf::Blake2s,
    signature::{Schnorr, SchnorrParameters, SchnorrPublicKey, SchnorrSignature},
};
use snarkvm_curves::traits::Group;
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::{
    serialize::{CanonicalDeserialize, CanonicalSerialize},
    to_bytes_le,
    FromBytes,
    ToBytes,
};

use digest::Digest;
use itertools::Itertools;
use std::{borrow::Borrow, marker::PhantomData};

#[derive(Clone)]
pub struct SchnorrParametersGadget<G: Group, F: Field, D: Digest> {
    parameters: SchnorrParameters<G, D>,
    _engine: PhantomData<*const F>,
}

impl<G: Group, F: Field, D: Digest> AllocGadget<SchnorrParameters<G, D>, F> for SchnorrParametersGadget<G, F, D> {
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<SchnorrParameters<G, D>>, CS: ConstraintSystem<F>>(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let parameters = value.borrow().clone();
        Ok(Self {
            parameters,
            _engine: PhantomData,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrParameters<G, D>>,
        CS: ConstraintSystem<F>,
    >(
        _cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let parameters = value.borrow().clone();
        Ok(Self {
            parameters,
            _engine: PhantomData,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchnorrPublicKeyGadget<G: Group, F: Field, GG: GroupGadget<G, F>> {
    public_key: GG,
    _group: PhantomData<G>,
    _engine: PhantomData<F>,
}

impl<G: Group + CanonicalSerialize + CanonicalDeserialize, F: Field, GG: GroupGadget<G, F>>
    AllocGadget<SchnorrPublicKey<G>, F> for SchnorrPublicKeyGadget<G, F, GG>
{
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<SchnorrPublicKey<G>>, CS: ConstraintSystem<F>>(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            public_key: GG::alloc_checked(cs, || f().map(|pk| pk.borrow().0))?,
            _engine: PhantomData,
            _group: PhantomData,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrPublicKey<G>>,
        CS: ConstraintSystem<F>,
    >(
        cs: CS,
        f: Fn,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            public_key: GG::alloc_input(cs, || f().map(|pk| pk.borrow().0))?,
            _engine: PhantomData,
            _group: PhantomData,
        })
    }
}

impl<G: Group, F: Field, GG: GroupGadget<G, F>> ConditionalEqGadget<F> for SchnorrPublicKeyGadget<G, F, GG> {
    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.public_key.conditional_enforce_equal(
            &mut cs.ns(|| "conditional_enforce_equal"),
            &other.public_key,
            condition,
        )?;
        Ok(())
    }

    fn cost() -> usize {
        <GG as ConditionalEqGadget<F>>::cost()
    }
}

impl<G: Group, F: Field, GG: GroupGadget<G, F>> EqGadget<F> for SchnorrPublicKeyGadget<G, F, GG> {}

impl<G: Group, F: Field, GG: GroupGadget<G, F>> ToBytesLEGadget<F> for SchnorrPublicKeyGadget<G, F, GG> {
    fn to_bytes_le<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.public_key.to_bytes_le(&mut cs.ns(|| "to_bytes"))
    }

    fn to_bytes_le_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.public_key.to_bytes_le_strict(&mut cs.ns(|| "to_bytes_strict"))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchnorrSignatureGadget<G: Group, F: Field, FG: FieldGadget<F, F>> {
    prover_response: FG,
    verifier_challenge: FG,
    _field: PhantomData<*const F>,
    _group: PhantomData<*const G>,
}

impl<G: Group, F: Field, FG: FieldGadget<F, F>> AllocGadget<SchnorrSignature<G>, F>
    for SchnorrSignatureGadget<G, F, FG>
{
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<SchnorrSignature<G>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let schnorr_output = value.borrow().clone();

        // TODO (raychu86): Check that this conversion is valid.
        //  This will work for EdwardsBls Fr and Bls12_377 Fr because they are both represented with Fp256.
        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read_le(&to_bytes_le![schnorr_output.prover_response]?[..])?;
        let verifier_challenge: F = FromBytes::read_le(&to_bytes_le![schnorr_output.verifier_challenge]?[..])?;

        let prover_response = FG::alloc(cs.ns(|| "alloc_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge = FG::alloc(cs.ns(|| "alloc_verifier_challenge"), || Ok(&verifier_challenge))?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            _field: PhantomData,
            _group: PhantomData,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrSignature<G>>,
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

        let prover_response = FG::alloc_input(cs.ns(|| "alloc_input_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FG::alloc_input(cs.ns(|| "alloc_input_verifier_challenge"), || Ok(&verifier_challenge))?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            _field: PhantomData,
            _group: PhantomData,
        })
    }
}

impl<G: Group, F: Field, FG: FieldGadget<F, F>> ConditionalEqGadget<F> for SchnorrSignatureGadget<G, F, FG> {
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
        <FG as ConditionalEqGadget<F>>::cost() * 2
    }
}

impl<G: Group, F: Field, FG: FieldGadget<F, F>> EqGadget<F> for SchnorrSignatureGadget<G, F, FG> {}

impl<G: Group, F: Field, FG: FieldGadget<F, F>> ToBytesLEGadget<F> for SchnorrSignatureGadget<G, F, FG> {
    fn to_bytes_le<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut result = Vec::new();

        result.extend(
            self.prover_response
                .to_bytes_le(&mut cs.ns(|| "prover_response_to_bytes"))?,
        );
        result.extend(
            self.verifier_challenge
                .to_bytes_le(&mut cs.ns(|| "verifier_challenge_to_bytes"))?,
        );

        Ok(result)
    }

    fn to_bytes_le_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut result = Vec::new();

        result.extend(
            self.prover_response
                .to_bytes_le_strict(&mut cs.ns(|| "prover_response_to_bytes_strict"))?,
        );
        result.extend(
            self.verifier_challenge
                .to_bytes_le_strict(&mut cs.ns(|| "verifier_challenge_to_bytes_strict"))?,
        );

        Ok(result)
    }
}

pub struct SchnorrPublicKeyRandomizationGadget<G: Group, F: PrimeField, GG: GroupGadget<G, F>, FG: FieldGadget<F, F>> {
    _group: PhantomData<*const G>,
    _group_gadget: PhantomData<*const GG>,
    _field_gadget: PhantomData<*const FG>,
    _engine: PhantomData<*const F>,
}

impl<
    G: Group + CanonicalSerialize + CanonicalDeserialize,
    GG: GroupGadget<G, F>,
    FG: FieldGadget<F, F>,
    D: Digest + Send + Sync,
    F: PrimeField,
> SignaturePublicKeyRandomizationGadget<Schnorr<G, D>, F> for SchnorrPublicKeyRandomizationGadget<G, F, GG, FG>
{
    type ParametersGadget = SchnorrParametersGadget<G, F, D>;
    type PublicKeyGadget = SchnorrPublicKeyGadget<G, F, GG>;
    type SignatureGadget = SchnorrSignatureGadget<G, F, FG>;

    fn check_randomization_gadget<CS: ConstraintSystem<F>>(
        mut cs: CS,
        parameters: &Self::ParametersGadget,
        public_key: &Self::PublicKeyGadget,
        randomness: &[UInt8],
    ) -> Result<Self::PublicKeyGadget, SynthesisError> {
        let randomness = randomness.iter().flat_map(|b| b.u8_to_bits_le()).collect::<Vec<_>>();
        let mut rand_pk = public_key.public_key.clone();
        rand_pk.scalar_multiplication(
            cs.ns(|| "check_randomization_gadget"),
            randomness.iter().zip_eq(&parameters.parameters.generator_powers),
        )?;

        Ok(SchnorrPublicKeyGadget {
            public_key: rand_pk,
            _group: PhantomData,
            _engine: PhantomData,
        })
    }

    // TODO (raychu86): Make the blake2s usage generic for all PRFs.
    fn verify<CS: ConstraintSystem<F>, PG: PRFGadget<Blake2s, F>>(
        mut cs: CS,
        parameters: &Self::ParametersGadget,
        public_key: &Self::PublicKeyGadget,
        message: &[UInt8],
        signature: &Self::SignatureGadget,
    ) -> Result<Boolean, SynthesisError> {
        let zero_group_gadget = GG::zero(cs.ns(|| "zero"))?;

        let prover_response_bytes = signature
            .prover_response
            .to_bytes_le(cs.ns(|| "prover_response_to_bytes"))?;

        let prover_response_bits = prover_response_bytes
            .iter()
            .flat_map(|byte| byte.u8_to_bits_le())
            .collect::<Vec<_>>();
        let verifier_challenge_bits = signature
            .verifier_challenge
            .to_bits_le(cs.ns(|| "verifier_challenge_to_bits"))?;

        let mut claimed_prover_commitment = GG::zero(cs.ns(|| "zero_claimed_prover_commitment"))?;
        for (i, (bit, base_power)) in prover_response_bits
            .iter()
            .zip_eq(&parameters.parameters.generator_powers)
            .enumerate()
        {
            let added =
                claimed_prover_commitment.add_constant(cs.ns(|| format!("add_base_power_{}", i)), base_power)?;

            claimed_prover_commitment = GG::conditionally_select(
                cs.ns(|| format!("cond_select_{}", i)),
                &bit,
                &added,
                &claimed_prover_commitment,
            )?;
        }

        let public_key_times_verifier_challenge = public_key.public_key.mul_bits(
            cs.ns(|| "record_view_key"),
            &zero_group_gadget,
            verifier_challenge_bits.into_iter(),
        )?;

        claimed_prover_commitment = claimed_prover_commitment.add(
            cs.ns(|| "claimed_prover_commitment_plus_public_key_times_verifier_challenge"),
            &public_key_times_verifier_challenge,
        )?;

        let salt_bytes = UInt8::alloc_vec(cs.ns(|| "alloc_salt"), &parameters.parameters.salt)?;
        let claimed_prover_commitment_bytes =
            claimed_prover_commitment.to_bytes_le(cs.ns(|| "claimed_prover_commitment_to_bytes"))?;

        // Construct the hash

        let mut hash_input = Vec::new();
        hash_input.extend_from_slice(&claimed_prover_commitment_bytes);
        hash_input.extend_from_slice(&message);

        let hash = PG::check_evaluation_gadget(cs.ns(|| "schnorr_hash"), &salt_bytes, &hash_input)?;

        // Check that the hash bytes are equivalent to the Field gadget.

        let hash_bytes = hash.to_bytes_le(cs.ns(|| "hash_to_bytes"))?;
        let verifier_challenge_bytes = signature
            .verifier_challenge
            .to_bytes_le(cs.ns(|| "verifier_challenge_to_bytes"))?;

        let total_bits = <G as Group>::ScalarField::size_in_bits();
        let mut expected_bits = Vec::with_capacity(total_bits);
        let mut found_bits = Vec::with_capacity(total_bits);

        // Check all the bits up to the bit size of the Field gadget.
        for (i, (expected_byte, found_byte)) in verifier_challenge_bytes.iter().zip_eq(&hash_bytes).enumerate() {
            for (j, (expected_bit, found_bit)) in expected_byte
                .u8_to_bits_le()
                .iter()
                .zip_eq(found_byte.u8_to_bits_le())
                .enumerate()
            {
                if (i * 8 + j) < total_bits {
                    expected_bits.push(expected_bit.clone());
                    found_bits.push(found_bit.clone());
                }
            }
        }

        let result = expected_bits.is_eq(cs.ns(|| "is_eq"), &found_bits)?;

        return Ok(result);
    }
}
