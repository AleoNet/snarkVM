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
    algorithms::signature::schnorr::*,
    bits::{Boolean, ToBytesGadget},
    integers::uint::UInt8,
    traits::{
        algorithms::SignaturePublicKeyRandomizationGadget,
        alloc::AllocGadget,
        curves::GroupGadget,
        eq::EqGadget,
        integers::Integer,
    },
    FieldGadget,
    PRFGadget,
};
use snarkvm_algorithms::prf::Blake2s;
use snarkvm_curves::traits::Group;
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::serialize::{CanonicalDeserialize, CanonicalSerialize};

use digest::Digest;
use itertools::Itertools;
use snarkvm_algorithms::encryption::{GroupEncryption, GroupEncryptionParameters, GroupEncryptionPublicKey};
use snarkvm_curves::ProjectiveCurve;
use std::{borrow::Borrow, marker::PhantomData};

#[derive(Clone)]
pub struct GroupEncryptionParametersGadget<G: Group, F: Field> {
    pub parameters: GroupEncryptionParameters<G>,
    _engine: PhantomData<*const F>,
}

impl<G: Group, F: Field> AllocGadget<GroupEncryptionParameters<G>, F> for GroupEncryptionParametersGadget<G, F> {
    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<GroupEncryptionParameters<G>>,
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

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<GroupEncryptionParameters<G>>,
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

impl<G: Group + ProjectiveCurve + CanonicalSerialize + CanonicalDeserialize, F: Field, GG: GroupGadget<G, F>>
    AllocGadget<GroupEncryptionPublicKey<G>, F> for SchnorrPublicKeyGadget<G, F, GG>
{
    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<GroupEncryptionPublicKey<G>>,
        CS: ConstraintSystem<F>,
    >(
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
        T: Borrow<GroupEncryptionPublicKey<G>>,
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

// TODO (raychu86): Make this implementation generic for both GroupEncryption and Schnorr Signature.
impl<
    G: Group + CanonicalSerialize + CanonicalDeserialize + ProjectiveCurve,
    GG: GroupGadget<G, F>,
    FG: FieldGadget<F, F>,
    D: Digest + Send + Sync,
    F: PrimeField,
> SignaturePublicKeyRandomizationGadget<GroupEncryption<G, G, D>, F>
    for SchnorrPublicKeyRandomizationGadget<G, F, GG, FG>
{
    type ParametersGadget = GroupEncryptionParametersGadget<G, F>;
    type PublicKeyGadget = SchnorrPublicKeyGadget<G, F, GG>;
    type SignatureGadget = SchnorrSignatureGadget<G, F, FG>;

    fn check_randomization_gadget<CS: ConstraintSystem<F>>(
        mut cs: CS,
        parameters: &Self::ParametersGadget,
        public_key: &Self::PublicKeyGadget,
        randomness: &[UInt8],
    ) -> Result<Self::PublicKeyGadget, SynthesisError> {
        let randomness = randomness.iter().flat_map(|b| b.to_bits_le()).collect::<Vec<_>>();
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
            .to_bytes(cs.ns(|| "prover_response_to_bytes"))?;

        let prover_response_bits = prover_response_bytes
            .iter()
            .flat_map(|byte| byte.to_bits_le())
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
            claimed_prover_commitment.to_bytes(cs.ns(|| "claimed_prover_commitment_to_bytes"))?;

        // Construct the hash

        let mut hash_input = Vec::new();
        hash_input.extend_from_slice(&claimed_prover_commitment_bytes);
        hash_input.extend_from_slice(&message);

        let hash = PG::check_evaluation_gadget(cs.ns(|| "schnorr_hash"), &salt_bytes, &hash_input)?;

        // Check that the hash bytes are equivalent to the Field gadget.

        let hash_bytes = hash.to_bytes(cs.ns(|| "hash_to_bytes"))?;
        let verifier_challenge_bytes = signature
            .verifier_challenge
            .to_bytes(cs.ns(|| "verifier_challenge_to_bytes"))?;

        let total_bits = <G as Group>::ScalarField::size_in_bits();
        let mut expected_bits = Vec::with_capacity(total_bits);
        let mut found_bits = Vec::with_capacity(total_bits);

        // Check all the bits up to the bit size of the Field gadget.
        for (i, (expected_byte, found_byte)) in verifier_challenge_bytes.iter().zip_eq(&hash_bytes).enumerate() {
            for (j, (expected_bit, found_bit)) in expected_byte
                .to_bits_le()
                .iter()
                .zip_eq(found_byte.to_bits_le())
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
