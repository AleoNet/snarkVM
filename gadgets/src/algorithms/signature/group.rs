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
    algorithms::crypto_hash::{CryptographicSpongeVar, PoseidonSpongeGadget},
    bits::{Boolean, ToBytesGadget},
    integers::uint::UInt8,
    traits::{
        algorithms::SignaturePublicKeyRandomizationGadget,
        alloc::AllocGadget,
        curves::GroupGadget,
        eq::EqGadget,
        integers::Integer,
    },
    ConditionalEqGadget,
    FpGadget,
    ToBitsLEGadget,
    ToConstraintFieldGadget,
};
use snarkvm_algorithms::{
    crypto_hash::PoseidonDefaultParametersField,
    encryption::{GroupEncryption, GroupEncryptionParameters, GroupEncryptionPublicKey},
    signature::SchnorrSignature,
};
use snarkvm_curves::{traits::Group, AffineCurve, ProjectiveCurve};
use snarkvm_fields::{Field, FieldParameters, PrimeField, ToConstraintField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};
use snarkvm_utilities::{
    serialize::{CanonicalDeserialize, CanonicalSerialize},
    to_bytes,
    FromBytes,
    ToBytes,
};

use itertools::Itertools;
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroupEncryptionPublicKeyGadget<G: Group, F: Field, GG: GroupGadget<G, F>> {
    pub(crate) public_key: GG,
    pub(crate) _group: PhantomData<G>,
    pub(crate) _engine: PhantomData<F>,
}

impl<G: Group + ProjectiveCurve + CanonicalSerialize + CanonicalDeserialize, F: Field, GG: GroupGadget<G, F>>
    AllocGadget<GroupEncryptionPublicKey<G>, F> for GroupEncryptionPublicKeyGadget<G, F, GG>
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

impl<G: Group, F: Field, GG: GroupGadget<G, F>> ConditionalEqGadget<F> for GroupEncryptionPublicKeyGadget<G, F, GG> {
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

impl<G: Group, F: Field, GG: GroupGadget<G, F>> EqGadget<F> for GroupEncryptionPublicKeyGadget<G, F, GG> {}

impl<G: Group, F: Field, GG: GroupGadget<G, F>> ToBytesGadget<F> for GroupEncryptionPublicKeyGadget<G, F, GG> {
    fn to_bytes<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.public_key.to_bytes(&mut cs.ns(|| "to_bytes"))
    }

    fn to_bytes_strict<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        self.public_key.to_bytes_strict(&mut cs.ns(|| "to_bytes_strict"))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroupEncryptionSignatureGadget<G: Group, SG: Group, F: PrimeField> {
    pub(crate) prover_response: FpGadget<F>,
    pub(crate) verifier_challenge: FpGadget<F>,
    pub(crate) _field: PhantomData<*const F>,
    pub(crate) _group: PhantomData<*const G>,
    pub(crate) _signature_group: PhantomData<*const SG>,
}

impl<G: Group, SG: Group, F: PrimeField> AllocGadget<SchnorrSignature<SG>, F>
    for GroupEncryptionSignatureGadget<G, SG, F>
{
    fn alloc<Fn: FnOnce() -> Result<T, SynthesisError>, T: Borrow<SchnorrSignature<SG>>, CS: ConstraintSystem<F>>(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let schnorr_output = value.borrow().clone();

        // TODO (raychu86): Check that this conversion is valid.
        //  This will work for EdwardsBls Fr and Bls12_377 Fr because they are both represented with Fp256.
        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read(&to_bytes![schnorr_output.prover_response]?[..])?;
        let verifier_challenge: F = FromBytes::read(&to_bytes![schnorr_output.verifier_challenge]?[..])?;

        let prover_response = FpGadget::<F>::alloc(cs.ns(|| "alloc_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FpGadget::<F>::alloc(cs.ns(|| "alloc_verifier_challenge"), || Ok(&verifier_challenge))?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            _field: PhantomData,
            _group: PhantomData,
            _signature_group: PhantomData,
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SchnorrSignature<SG>>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        let value = value_gen()?;
        let schnorr_output = value.borrow().clone();

        // Cast <G as Group>::ScalarField as F.
        let prover_response: F = FromBytes::read(&to_bytes![schnorr_output.prover_response]?[..])?;
        let verifier_challenge: F = FromBytes::read(&to_bytes![schnorr_output.verifier_challenge]?[..])?;

        let prover_response =
            FpGadget::<F>::alloc_input(cs.ns(|| "alloc_input_prover_response"), || Ok(&prover_response))?;
        let verifier_challenge =
            FpGadget::<F>::alloc_input(cs.ns(|| "alloc_input_verifier_challenge"), || Ok(&verifier_challenge))?;

        Ok(Self {
            prover_response,
            verifier_challenge,
            _field: PhantomData,
            _group: PhantomData,
            _signature_group: PhantomData,
        })
    }
}

impl<G: Group, SG: Group, F: PrimeField> ConditionalEqGadget<F> for GroupEncryptionSignatureGadget<G, SG, F> {
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

impl<G: Group, SG: Group, F: PrimeField> EqGadget<F> for GroupEncryptionSignatureGadget<G, SG, F> {}

impl<G: Group, SG: Group, F: PrimeField> ToBytesGadget<F> for GroupEncryptionSignatureGadget<G, SG, F> {
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

pub struct GroupEncryptionPublicKeyRandomizationGadget<G: Group, SG: Group, F: PrimeField, GG: GroupGadget<G, F>> {
    pub(crate) _group: PhantomData<*const G>,
    pub(crate) _signature_group: PhantomData<*const SG>,
    pub(crate) _group_gadget: PhantomData<*const GG>,
    pub(crate) _engine: PhantomData<*const F>,
}

impl<
    G: Group + CanonicalSerialize + CanonicalDeserialize + ProjectiveCurve,
    SG: Group + CanonicalSerialize + CanonicalDeserialize + AffineCurve,
    GG: GroupGadget<G, F> + ToConstraintFieldGadget<F>,
    F: PrimeField + PoseidonDefaultParametersField,
> SignaturePublicKeyRandomizationGadget<GroupEncryption<G, SG>, F>
    for GroupEncryptionPublicKeyRandomizationGadget<G, SG, F, GG>
where
    <SG as AffineCurve>::BaseField: PoseidonDefaultParametersField,
    SG: ToConstraintField<<SG as AffineCurve>::BaseField>,
{
    type ParametersGadget = GroupEncryptionParametersGadget<G, F>;
    type PublicKeyGadget = GroupEncryptionPublicKeyGadget<G, F, GG>;
    type SignatureGadget = GroupEncryptionSignatureGadget<G, SG, F>;

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

        Ok(GroupEncryptionPublicKeyGadget {
            public_key: rand_pk,
            _group: PhantomData,
            _engine: PhantomData,
        })
    }

    fn verify<CS: ConstraintSystem<F>>(
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

        // Construct the hash
        let mut hash_input = {
            let salt_bytes_field_elements: Vec<F> = parameters.parameters.salt.to_field_elements().unwrap();

            let mut res = Vec::new();
            for (i, elem) in salt_bytes_field_elements.iter().enumerate() {
                res.push(FpGadget::<F>::alloc_constant(
                    cs.ns(|| format!("alloc salt byte field element {}", i)),
                    || Ok((*elem).clone()),
                )?);
            }
            res
        };
        hash_input.extend_from_slice(
            &claimed_prover_commitment
                .to_constraint_field(cs.ns(|| "convert claimed_prover_commitment into field elements"))?,
        );
        hash_input.extend_from_slice(&message.to_constraint_field(cs.ns(|| "convert message into field elements"))?);

        // Compute the hash on the base field
        let params = F::get_default_poseidon_parameters(4, false).unwrap();
        let mut sponge = PoseidonSpongeGadget::<F>::new(cs.ns(|| "alloc sponge"), &params);
        sponge.absorb(cs.ns(|| "absorb"), hash_input.iter())?;
        let raw_hash = {
            let res = sponge.squeeze_field_elements(cs.ns(|| "squeeze"), 1)?;
            res[0].clone()
        };

        // Bit decompose the raw_hash
        let mut raw_hash_bits = raw_hash.to_bits_le(cs.ns(|| "convert the hash into bits"))?;
        raw_hash_bits.resize(
            <G::ScalarField as PrimeField>::Parameters::CAPACITY as usize,
            Boolean::Constant(false),
        );

        let hash = Boolean::le_bits_to_fp_var(cs.ns(|| "obtain the truncated hash"), &raw_hash_bits)?;
        let result = signature
            .verifier_challenge
            .is_eq(cs.ns(|| "check verifier challenge"), &hash)?;

        return Ok(result);
    }
}
