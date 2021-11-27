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
    crypto_hash::{PoseidonDefaultParametersField, PoseidonParameters, PoseidonSponge},
    hash_to_curve::hash_to_curve,
    AlgebraicSponge,
    EncryptionError,
    EncryptionScheme,
};
use rand::{CryptoRng, Rng};
use snarkvm_curves::{
    templates::twisted_edwards_extended::{Affine as TEAffine, Projective},
    AffineCurve,
    ProjectiveCurve,
    TwistedEdwardsParameters,
};
use snarkvm_fields::{ConstraintFieldError, FieldParameters, PrimeField, ToConstraintField, Zero};
use snarkvm_utilities::{
    io::Result as IoResult,
    ops::Mul,
    serialize::*,
    BitIteratorBE,
    FromBytes,
    Read,
    SerializationError,
    ToBytes,
    UniformRand,
    Write,
};

use std::sync::Arc;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Copy(bound = "TE: TwistedEdwardsParameters"),
    Clone(bound = "TE: TwistedEdwardsParameters"),
    PartialEq(bound = "TE: TwistedEdwardsParameters"),
    Eq(bound = "TE: TwistedEdwardsParameters"),
    Debug(bound = "TE: TwistedEdwardsParameters"),
    Hash(bound = "TE: TwistedEdwardsParameters")
)]
pub struct ECIESPoseidonPublicKey<TE: TwistedEdwardsParameters>(pub TEAffine<TE>);

impl<TE: TwistedEdwardsParameters> ToBytes for ECIESPoseidonPublicKey<TE> {
    /// Writes the x-coordinate of the encryption public key.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.to_x_coordinate().write_le(&mut writer)
    }
}

impl<TE: TwistedEdwardsParameters> FromBytes for ECIESPoseidonPublicKey<TE> {
    /// Reads the x-coordinate of the encryption public key.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let x_coordinate = TE::BaseField::read_le(&mut reader)?;

        if let Some(element) = TEAffine::<TE>::from_x_coordinate(x_coordinate, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(Self(element));
            }
        }

        if let Some(element) = TEAffine::<TE>::from_x_coordinate(x_coordinate, false) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(Self(element));
            }
        }

        Err(EncryptionError::Message("Failed to read encryption public key".into()).into())
    }
}

impl<TE: TwistedEdwardsParameters> Default for ECIESPoseidonPublicKey<TE> {
    fn default() -> Self {
        Self(TEAffine::<TE>::default())
    }
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "TE: TwistedEdwardsParameters"),
    Debug(bound = "TE: TwistedEdwardsParameters"),
    PartialEq(bound = "TE: TwistedEdwardsParameters"),
    Eq(bound = "TE: TwistedEdwardsParameters")
)]
pub struct ECIESPoseidonEncryption<TE: TwistedEdwardsParameters>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    pub generator: TEAffine<TE>,
    poseidon_parameters: Arc<PoseidonParameters<TE::BaseField, 4, 1>>,
}

impl<TE: TwistedEdwardsParameters> ECIESPoseidonEncryption<TE>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    const SENTINEL: u8 = 1;
}

impl<TE: TwistedEdwardsParameters> EncryptionScheme for ECIESPoseidonEncryption<TE>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    type CiphertextRandomizer = TE::BaseField;
    type Parameters = TEAffine<TE>;
    type PrivateKey = TE::ScalarField;
    type PublicKey = TEAffine<TE>;
    type ScalarRandomness = TE::ScalarField;
    type SymmetricKey = TE::BaseField;

    fn setup(message: &str) -> Self {
        let (generator, _, _) = hash_to_curve::<TEAffine<TE>>(message);
        let poseidon_parameters = Arc::new(
            <TE::BaseField as PoseidonDefaultParametersField>::get_default_poseidon_parameters::<4>(false).unwrap(),
        );

        Self {
            generator,
            poseidon_parameters,
        }
    }

    fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> Self::PrivateKey {
        Self::PrivateKey::rand(rng)
    }

    fn generate_public_key(&self, private_key: &Self::PrivateKey) -> Self::PublicKey {
        self.generator.into_projective().mul(*private_key).into_affine()
    }

    /// Given an RNG, returns the following:
    ///
    ///                  randomness := r
    ///       ciphertext_randomizer := G^r
    ///               symmetric_key := public_key^r == G^ar
    ///
    fn generate_asymmetric_key<R: Rng + CryptoRng>(
        &self,
        public_key: &Self::PublicKey,
        rng: &mut R,
    ) -> (Self::ScalarRandomness, Self::CiphertextRandomizer, Self::SymmetricKey) {
        // Sample randomness.
        let randomness: Self::ScalarRandomness = UniformRand::rand(rng);

        // Compute the randomizer := G^r
        let ciphertext_randomizer = self
            .generator
            .mul_bits(BitIteratorBE::new_without_leading_zeros(randomness.to_repr()));

        // Compute the ECDH value := public_key^r.
        // Note for twisted Edwards curves, only one of (x, y) or (x, -y) is in the prime-order subgroup.
        let symmetric_key = public_key.mul_bits(BitIteratorBE::new_without_leading_zeros(randomness.to_repr()));

        let mut batch = [ciphertext_randomizer, symmetric_key];
        Projective::<TE>::batch_normalization(&mut batch);
        let (ciphertext_randomizer, symmetric_key) = (
            batch[0].into_affine().to_x_coordinate(),
            batch[1].into_affine().to_x_coordinate(),
        );

        (randomness, ciphertext_randomizer, symmetric_key)
    }

    /// Given the private key and ciphertext randomizer, return the following:
    ///
    ///    symmetric_key := public_key^r == (G^r)^private_key
    ///
    fn generate_symmetric_key(
        &self,
        private_key: &<Self as EncryptionScheme>::PrivateKey,
        ciphertext_randomizer: Self::CiphertextRandomizer,
    ) -> Result<Self::SymmetricKey, EncryptionError> {
        // Recover the ciphertext randomizer group element.
        let randomizer = {
            let mut first = TEAffine::<TE>::from_x_coordinate(ciphertext_randomizer, true);
            if first.is_some() && !first.unwrap().is_in_correct_subgroup_assuming_on_curve() {
                first = None;
            }
            let mut second = TEAffine::<TE>::from_x_coordinate(ciphertext_randomizer, false);
            if second.is_some() && !second.unwrap().is_in_correct_subgroup_assuming_on_curve() {
                second = None;
            }
            let randomizer = first.or(second);
            if randomizer.is_none() {
                return Err(EncryptionError::Message(
                    "The ciphertext randomizer is malformed.".to_string(),
                ));
            }
            randomizer.unwrap()
        };

        // Compute the ECDH value.
        Ok(randomizer
            .mul_bits(BitIteratorBE::new_without_leading_zeros(private_key.to_repr()))
            .into_affine()
            .to_x_coordinate())
    }

    /// Encrypts the given message, and returns the following:
    ///
    ///     ciphertext := to_bytes_le![C_1, ..., C_n], where C_i := R_i + M_i, and R_i := H_i(G^ar)
    ///
    fn encrypt(&self, symmetric_key: &Self::SymmetricKey, message: &[u8]) -> Result<Vec<u8>, EncryptionError> {
        // Initialize sponge state.
        let mut sponge = PoseidonSponge::with_parameters(&self.poseidon_parameters);
        let domain_separator = TE::BaseField::from_bytes_le_mod_order(b"AleoEncryption2021");
        sponge.absorb(&[domain_separator, *symmetric_key]);

        // Determine the number of bytes that fit in each field element.
        let bit_capacity = <<TE::BaseField as PrimeField>::Parameters>::CAPACITY as usize;
        let byte_capacity = bit_capacity / 8;
        let modulus_bits = <<TE::BaseField as PrimeField>::Parameters>::MODULUS_BITS as usize;
        let bytes_per_field_element = ((modulus_bits + 63) / 64) * 8;

        // Add a sentinel to indicate the start of the padding.
        let mut message = message.to_vec();
        message.push(Self::SENTINEL);

        // Obtain random field elements from Poseidon.
        // Pack the bytes into field elements and add the random field elements to the packed bits.
        let ciphertext = message
            .chunks(byte_capacity)
            .flat_map(|chunk| {
                let sponge_randomizer = sponge.squeeze_field_elements(1)[0];
                let plaintext_element = TE::BaseField::from_bytes_le_mod_order(&chunk);
                (plaintext_element + sponge_randomizer).to_bytes_le().unwrap()
            })
            .collect::<Vec<_>>();

        let num_field_elements = (message.len() + byte_capacity - 1) / byte_capacity;
        let num_bytes = num_field_elements * bytes_per_field_element;

        assert_eq!(ciphertext.len(), num_bytes, "incorrect length for ciphertext");

        Ok(ciphertext)
    }

    /// Decrypt while the condition specified by `f` is satisfied.
    fn decrypt_while(
        &self,
        symmetric_key: &Self::SymmetricKey,
        ciphertext: &[u8],
        should_continue: impl Fn(&[u8]) -> bool,
    ) -> Result<Vec<u8>, EncryptionError> {
        let bit_capacity = <<TE::BaseField as PrimeField>::Parameters>::CAPACITY as usize;
        let modulus_bits = <<TE::BaseField as PrimeField>::Parameters>::MODULUS_BITS as usize;
        let byte_capacity_less_than_modulus = bit_capacity / 8;
        let byte_capacity_more_than_modulus = (modulus_bits + 8 - 1) / 8;
        let bytes_per_field_element = ((modulus_bits + 63) / 64) * 8;
        assert!(ciphertext.len() >= byte_capacity_more_than_modulus);

        // Initialize sponge state.
        let mut sponge = PoseidonSponge::with_parameters(&self.poseidon_parameters);
        let domain_separator = TE::BaseField::from_bytes_le_mod_order(b"AleoEncryption2021");
        sponge.absorb(&[domain_separator, *symmetric_key]);

        // Subtract the random field elements to the packed bits.
        assert_eq!(ciphertext.len() % bytes_per_field_element, 0);
        let num_chunks = ciphertext.len() / bytes_per_field_element;

        let mut plaintext = Vec::with_capacity(ciphertext.len());
        for (i, chunk) in ciphertext.chunks(bytes_per_field_element).enumerate() {
            let ciphertext_block = TE::BaseField::from_bytes_le(chunk).unwrap();
            let sponge_fe = sponge.squeeze_field_elements(1)[0];
            let plaintext_fe = ciphertext_block - sponge_fe;
            let bytes = &plaintext_fe.to_bytes_le()?[..byte_capacity_less_than_modulus];
            let mut sentinel_index = bytes.len();
            if i == num_chunks - 1 {
                // If we're in the last chunk, truncate the padding
                if plaintext_fe.is_zero() {
                    Err(EncryptionError::Message(
                        "The packed field elements must end with a non-zero element.".into(),
                    ))?;
                }
                for (i, byte) in bytes.iter().enumerate().rev() {
                    if byte == &Self::SENTINEL {
                        sentinel_index = i;
                        break;
                    }
                }
            }
            plaintext.extend_from_slice(&bytes[..sentinel_index]);

            if !should_continue(&plaintext) {
                return Err(EncryptionError::MismatchingAddress);
            }
        }
        if plaintext.is_empty() {
            Err(EncryptionError::Message(
                "The packed field elements must consist of at least one field element.".into(),
            ))?;
        }

        let num_field_elements =
            (plaintext.len() + byte_capacity_less_than_modulus - 1) / byte_capacity_less_than_modulus;
        let num_bytes = num_field_elements * bytes_per_field_element;
        assert_eq!(ciphertext.len(), num_bytes);

        Ok(plaintext)
    }

    fn parameters(&self) -> &<Self as EncryptionScheme>::Parameters {
        &self.generator
    }

    fn private_key_size_in_bits() -> usize {
        Self::PrivateKey::size_in_bits()
    }
}

impl<TE: TwistedEdwardsParameters> From<TEAffine<TE>> for ECIESPoseidonEncryption<TE>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    fn from(generator: TEAffine<TE>) -> Self {
        let poseidon_parameters = Arc::new(
            <TE::BaseField as PoseidonDefaultParametersField>::get_default_poseidon_parameters::<4>(false).unwrap(),
        );
        Self {
            generator,
            poseidon_parameters,
        }
    }
}

impl<TE: TwistedEdwardsParameters> ToBytes for ECIESPoseidonEncryption<TE>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.generator.write_le(&mut writer)
    }
}

impl<TE: TwistedEdwardsParameters> FromBytes for ECIESPoseidonEncryption<TE>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    #[inline]
    fn read_le<R: Read>(reader: R) -> IoResult<Self> {
        Ok(Self::from(TEAffine::<TE>::read_le(reader)?))
    }
}

impl<TE: TwistedEdwardsParameters> ToConstraintField<TE::BaseField> for ECIESPoseidonEncryption<TE>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<TE::BaseField>, ConstraintFieldError> {
        Ok(Vec::new())
    }
}
