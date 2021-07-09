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
    crypto_hash::PoseidonDefaultParametersField,
    signature::SchnorrParameters,
    CryptoHash,
    SignatureError,
    SignatureScheme,
};
use snarkvm_curves::traits::Group;
use snarkvm_fields::{ConstraintFieldError, Field, FieldParameters, One, PrimeField, ToConstraintField, Zero};
use snarkvm_utilities::{
    bytes::{from_bytes_le_to_bits_le, FromBytes, ToBytes},
    errors::SerializationError,
    rand::UniformRand,
    serialize::*,
    to_bytes,
    BigInteger,
};

use crate::crypto_hash::PoseidonCryptoHash;
use itertools::Itertools;
use rand::Rng;
use snarkvm_curves::AffineCurve;
use std::{
    hash::Hash,
    io::{Read, Result as IoResult, Write},
};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "G: Group"),
    Debug(bound = "G: Group"),
    Default(bound = "G: Group"),
    PartialEq(bound = "G: Group"),
    Eq(bound = "G: Group")
)]
pub struct SchnorrSignature<G: Group> {
    pub prover_response: <G as Group>::ScalarField,
    pub verifier_challenge: <G as Group>::ScalarField,
}

impl<G: Group> ToBytes for SchnorrSignature<G> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.prover_response.write(&mut writer)?;
        self.verifier_challenge.write(&mut writer)
    }
}

impl<G: Group> FromBytes for SchnorrSignature<G> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let prover_response = <G as Group>::ScalarField::read(&mut reader)?;
        let verifier_challenge = <G as Group>::ScalarField::read(&mut reader)?;

        Ok(Self {
            prover_response,
            verifier_challenge,
        })
    }
}

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Copy(bound = "G: Group"),
    Clone(bound = "G: Group"),
    PartialEq(bound = "G: Group"),
    Eq(bound = "G: Group"),
    Debug(bound = "G: Group"),
    Hash(bound = "G: Group"),
    Default(bound = "G: Group")
)]
pub struct SchnorrPublicKey<G: Group + CanonicalSerialize + CanonicalDeserialize>(pub G);

impl<G: Group + CanonicalSerialize + CanonicalDeserialize> ToBytes for SchnorrPublicKey<G> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write(&mut writer)
    }
}

impl<G: Group + CanonicalSerialize + CanonicalDeserialize> FromBytes for SchnorrPublicKey<G> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self(G::read(&mut reader)?))
    }
}

impl<F: Field, G: Group + CanonicalSerialize + CanonicalDeserialize + ToConstraintField<F>> ToConstraintField<F>
    for SchnorrPublicKey<G>
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        self.0.to_field_elements()
    }
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "G: Group"),
    Debug(bound = "G: Group"),
    PartialEq(bound = "G: Group"),
    Eq(bound = "G: Group")
)]
pub struct Schnorr<G: Group> {
    pub parameters: SchnorrParameters<G>,
}

impl<G: Group + Hash + CanonicalSerialize + CanonicalDeserialize + AffineCurve> SignatureScheme for Schnorr<G>
where
    <G as AffineCurve>::BaseField: PoseidonDefaultParametersField,
    G: ToConstraintField<<G as AffineCurve>::BaseField>,
{
    type Parameters = SchnorrParameters<G>;
    type PrivateKey = <G as Group>::ScalarField;
    type PublicKey = SchnorrPublicKey<G>;
    type Signature = SchnorrSignature<G>;

    fn setup<R: Rng>(rng: &mut R) -> Result<Self, SignatureError> {
        assert!(
            <<G as Group>::ScalarField as PrimeField>::Parameters::CAPACITY
                < <<G as AffineCurve>::BaseField as PrimeField>::Parameters::CAPACITY
        );

        let setup_time = start_timer!(|| "SchnorrSignature::setup");
        let parameters = Self::Parameters::setup(rng, Self::PrivateKey::size_in_bits());
        end_timer!(setup_time);

        Ok(Self { parameters })
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.parameters
    }

    fn generate_private_key<R: Rng>(&self, rng: &mut R) -> Result<Self::PrivateKey, SignatureError> {
        let keygen_time = start_timer!(|| "SchnorrSignature::generate_private_key");
        let private_key = <G as Group>::ScalarField::rand(rng);
        end_timer!(keygen_time);
        Ok(private_key)
    }

    fn generate_public_key(&self, private_key: &Self::PrivateKey) -> Result<Self::PublicKey, SignatureError> {
        let keygen_time = start_timer!(|| "SchnorrSignature::generate_public_key");

        let mut public_key = G::zero();
        for (bit, base_power) in
            from_bytes_le_to_bits_le(&to_bytes![private_key]?).zip_eq(&self.parameters.generator_powers)
        {
            if bit {
                public_key += base_power;
            }
        }
        end_timer!(keygen_time);

        Ok(SchnorrPublicKey(public_key))
    }

    fn sign<R: Rng>(
        &self,
        private_key: &Self::PrivateKey,
        message: &[u8],
        rng: &mut R,
    ) -> Result<Self::Signature, SignatureError> {
        let sign_time = start_timer!(|| "SchnorrSignature::sign");
        // (k, e);

        // Sample a random scalar `k` from the prime scalar field.
        let random_scalar: <G as Group>::ScalarField = <G as Group>::ScalarField::rand(rng);
        // Commit to the random scalar via r := k · g.
        // This is the prover's first msg in the Sigma protocol.
        let mut prover_commitment = G::zero();
        for (bit, base_power) in
            from_bytes_le_to_bits_le(&to_bytes![random_scalar]?).zip_eq(&self.parameters.generator_powers)
        {
            if bit {
                prover_commitment += base_power;
            }
        }

        // Hash everything to get verifier challenge.
        let mut hash_input = Vec::<<G as AffineCurve>::BaseField>::new();
        hash_input.extend_from_slice(&self.parameters.salt.to_field_elements().unwrap());
        hash_input.extend_from_slice(&prover_commitment.to_field_elements().unwrap());
        hash_input.extend_from_slice(&message.to_field_elements().unwrap());

        let raw_hash =
            PoseidonCryptoHash::<<G as AffineCurve>::BaseField, 4, false>::evaluate_fixed_length_vector(&hash_input)
                .unwrap();

        // Bit decompose the raw_hash
        let mut raw_hash_bits = raw_hash.into_repr().to_bits_le();
        raw_hash_bits.resize(
            <<G as Group>::ScalarField as PrimeField>::Parameters::CAPACITY as usize,
            false,
        );
        raw_hash_bits.reverse();

        // Compute the supposed verifier response: e := H(salt || r || msg);
        let verifier_challenge = <<G as Group>::ScalarField as PrimeField>::from_repr(
            <<G as Group>::ScalarField as PrimeField>::BigInteger::from_bits_be(raw_hash_bits),
        )
        .unwrap();

        // k - xe;
        let prover_response = random_scalar - (verifier_challenge * private_key);
        let signature = SchnorrSignature {
            prover_response,
            verifier_challenge,
        };

        end_timer!(sign_time);
        Ok(signature)
    }

    fn verify(
        &self,
        public_key: &Self::PublicKey,
        message: &[u8],
        signature: &Self::Signature,
    ) -> Result<bool, SignatureError> {
        let verify_time = start_timer!(|| "SchnorrSignature::Verify");

        let SchnorrSignature {
            prover_response,
            verifier_challenge,
        } = signature;

        let mut claimed_prover_commitment = G::zero();
        for (bit, base_power) in
            from_bytes_le_to_bits_le(&to_bytes![prover_response]?).zip_eq(&self.parameters.generator_powers)
        {
            if bit {
                claimed_prover_commitment += base_power;
            }
        }

        let public_key_times_verifier_challenge = public_key.0.mul(*verifier_challenge);
        claimed_prover_commitment += public_key_times_verifier_challenge;

        // Hash everything to get verifier challenge.
        let mut hash_input = Vec::<<G as AffineCurve>::BaseField>::new();
        hash_input.extend_from_slice(&self.parameters.salt.to_field_elements().unwrap());
        hash_input.extend_from_slice(&claimed_prover_commitment.to_field_elements().unwrap());
        hash_input.extend_from_slice(&message.to_field_elements().unwrap());

        let raw_hash =
            PoseidonCryptoHash::<<G as AffineCurve>::BaseField, 4, false>::evaluate_fixed_length_vector(&hash_input)
                .unwrap();

        // Bit decompose the raw_hash
        let mut raw_hash_bits = raw_hash.into_repr().to_bits_le();
        raw_hash_bits.resize(
            <<G as Group>::ScalarField as PrimeField>::Parameters::CAPACITY as usize,
            false,
        );
        raw_hash_bits.reverse();

        // Compute the supposed verifier response: e := H(salt || r || msg);
        let obtained_verifier_challenge = <<G as Group>::ScalarField as PrimeField>::from_repr(
            <<G as Group>::ScalarField as PrimeField>::BigInteger::from_bits_be(raw_hash_bits),
        )
        .unwrap();

        end_timer!(verify_time);
        Ok(verifier_challenge == &obtained_verifier_challenge)
    }

    fn randomize_public_key(
        &self,
        public_key: &Self::PublicKey,
        randomness: &[u8],
    ) -> Result<Self::PublicKey, SignatureError> {
        let rand_pk_time = start_timer!(|| "SchnorrSignature::randomize_public_key");

        let mut randomized_pk = public_key.0;

        let mut encoded = G::zero();
        for (bit, base_power) in
            from_bytes_le_to_bits_le(&to_bytes![randomness]?).zip_eq(&self.parameters.generator_powers)
        {
            if bit {
                encoded += base_power;
            }
        }
        randomized_pk += encoded;

        end_timer!(rand_pk_time);

        Ok(SchnorrPublicKey(randomized_pk))
    }

    fn randomize_signature(
        &self,
        signature: &Self::Signature,
        randomness: &[u8],
    ) -> Result<Self::Signature, SignatureError> {
        let rand_signature_time = start_timer!(|| "SchnorrSignature::randomize_signature");
        let SchnorrSignature {
            prover_response,
            verifier_challenge,
        } = signature;
        let mut base = <G as Group>::ScalarField::one();
        let mut multiplier = <G as Group>::ScalarField::zero();
        for bit in from_bytes_le_to_bits_le(randomness) {
            if bit {
                multiplier += base;
            }
            base.double_in_place();
        }

        let new_sig = SchnorrSignature {
            prover_response: *prover_response - (*verifier_challenge * multiplier),
            verifier_challenge: *verifier_challenge,
        };
        end_timer!(rand_signature_time);
        Ok(new_sig)
    }
}

impl<G: Group> From<SchnorrParameters<G>> for Schnorr<G> {
    fn from(parameters: SchnorrParameters<G>) -> Self {
        Self { parameters }
    }
}
