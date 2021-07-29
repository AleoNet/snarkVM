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
    crypto_hash::{CryptographicSponge, PoseidonDefaultParametersField, PoseidonSponge},
    hash_to_curve::hash_to_curve,
    EncryptionError,
    EncryptionScheme,
};
use rand::{CryptoRng, Rng};
use snarkvm_curves::{
    templates::twisted_edwards_extended::Affine as TEAffine,
    AffineCurve,
    ProjectiveCurve,
    TwistedEdwardsParameters,
};
use snarkvm_fields::{ConstraintFieldError, FieldParameters, PrimeField, ToConstraintField};
use snarkvm_utilities::{
    io::Result as IoResult,
    ops::Mul,
    serialize::*,
    BigInteger,
    FromBytes,
    Read,
    SerializationError,
    ToBytes,
    UniformRand,
    Write,
};

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
        let x_coordinate = self.0.to_x_coordinate();
        x_coordinate.write_le(&mut writer)
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
    Eq(bound = "TE: TwistedEdwardsParameters"),
    Default(bound = "TE: TwistedEdwardsParameters")
)]
pub struct ECIESPoseidonEncryption<TE: TwistedEdwardsParameters> {
    pub generator: TEAffine<TE>,
}

impl<TE: TwistedEdwardsParameters> EncryptionScheme for ECIESPoseidonEncryption<TE>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    type Parameters = TEAffine<TE>;
    type PrivateKey = TE::ScalarField;
    type PublicKey = ECIESPoseidonPublicKey<TE>;
    type Randomness = TE::ScalarField;

    fn setup(message: &str) -> Self {
        let (generator, _, _) = hash_to_curve::<TEAffine<TE>>(message);
        Self { generator }
    }

    fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> <Self as EncryptionScheme>::PrivateKey {
        Self::PrivateKey::rand(rng)
    }

    fn generate_public_key(
        &self,
        private_key: &<Self as EncryptionScheme>::PrivateKey,
    ) -> Result<<Self as EncryptionScheme>::PublicKey, EncryptionError> {
        Ok(ECIESPoseidonPublicKey::<TE> {
            0: self.generator.into_projective().mul(*private_key).into_affine(),
        })
    }

    fn generate_randomness<R: Rng + CryptoRng>(
        &self,
        _public_key: &<Self as EncryptionScheme>::PublicKey,
        rng: &mut R,
    ) -> Result<Self::Randomness, EncryptionError> {
        Ok(Self::Randomness::rand(rng))
    }

    fn encrypt(
        &self,
        public_key: &<Self as EncryptionScheme>::PublicKey,
        randomness: &Self::Randomness,
        message: &[u8],
    ) -> Result<Vec<u8>, EncryptionError> {
        // Compute the ECDH value.
        let ecdh_value = public_key.0.into_projective().mul((*randomness).clone()).into_affine();

        // Prepare the Poseidon sponge.
        let params =
            <TE::BaseField as PoseidonDefaultParametersField>::get_default_poseidon_parameters(4, false).unwrap();
        let mut sponge = PoseidonSponge::<TE::BaseField>::new(&params);
        sponge.absorb(&[ecdh_value.x]); // For TE curves, only one of (x, y) and (x, -y) would be on the curve.

        // Compute the number of sponge elements needed.
        let capacity = <TE::BaseField as PrimeField>::Parameters::CAPACITY as usize;
        let random_byte_per_sponge_element = capacity / 8;
        let num_sponge_field_elements =
            (message.len() + random_byte_per_sponge_element - 1) / random_byte_per_sponge_element;

        // Obtain a mask from Poseidon.
        let sponge_field_elements = sponge.squeeze_field_elements(num_sponge_field_elements);
        let mut sponge_bytes = Vec::with_capacity(num_sponge_field_elements * random_byte_per_sponge_element);
        for elem in sponge_field_elements.iter() {
            sponge_bytes.extend_from_slice(&elem.to_bytes_le()?[..random_byte_per_sponge_element]);
        }

        // Apply the mask to the message.
        let mut masked_message = vec![0u8; message.len()];
        for (i, message_byte) in message.iter().enumerate() {
            masked_message[i] = sponge_bytes[i].wrapping_add(*message_byte);
        }

        // Put the bytes of the x coordinate of the randomness group element
        // into the beginning of the ciphertext.
        let random_element_bytes = self
            .generator
            .into_projective()
            .mul((*randomness).clone())
            .into_affine()
            .to_x_coordinate()
            .to_bytes_le()?;

        Ok([random_element_bytes, masked_message].concat())
    }

    fn decrypt(
        &self,
        private_key: &<Self as EncryptionScheme>::PrivateKey,
        ciphertext: &[u8],
    ) -> Result<Vec<u8>, EncryptionError> {
        let x_coordinate_len = <TE::BaseField as PrimeField>::BigInteger::NUM_LIMBS * 8;
        assert!(ciphertext.len() >= x_coordinate_len);

        // Recover the randomness group element.
        let random_elem_x = TE::BaseField::from_bytes_le(&ciphertext[..x_coordinate_len])?;
        let random_elem = {
            let mut first = TEAffine::<TE>::from_x_coordinate(random_elem_x.clone(), true);
            if first.is_some() && !first.unwrap().is_in_correct_subgroup_assuming_on_curve() {
                first = None;
            }
            let mut second = TEAffine::<TE>::from_x_coordinate(random_elem_x, false);
            if second.is_some() && !second.unwrap().is_in_correct_subgroup_assuming_on_curve() {
                second = None;
            }
            let random_elem = first.or(second);
            if random_elem.is_none() {
                return Err(EncryptionError::Message("The ciphertext is malformed.".to_string()));
            }
            random_elem.unwrap()
        };

        // Compute the ECDH value
        let ecdh_value = random_elem.into_projective().mul((*private_key).clone()).into_affine();

        // Prepare the Poseidon sponge.
        let params =
            <TE::BaseField as PoseidonDefaultParametersField>::get_default_poseidon_parameters(4, false).unwrap();
        let mut sponge = PoseidonSponge::<TE::BaseField>::new(&params);
        sponge.absorb(&[ecdh_value.x]); // For TE curves, only one of (x, y) and (x, -y) would be on the curve.

        // Compute the number of sponge elements needed.
        let capacity = <TE::BaseField as PrimeField>::Parameters::CAPACITY as usize;
        let random_byte_per_sponge_element = capacity / 8;
        let num_sponge_field_elements =
            (ciphertext.len() - x_coordinate_len + random_byte_per_sponge_element - 1) / random_byte_per_sponge_element;

        // Obtain a mask from Poseidon.
        let sponge_field_elements = sponge.squeeze_field_elements(num_sponge_field_elements);
        let mut sponge_bytes = Vec::with_capacity(num_sponge_field_elements * random_byte_per_sponge_element);
        for elem in sponge_field_elements.iter() {
            sponge_bytes.extend_from_slice(&elem.to_bytes_le()?[..random_byte_per_sponge_element]);
        }

        // Apply the mask to the message.
        let mut message = vec![0u8; ciphertext.len() - x_coordinate_len];
        for (i, ciphertext_byte) in ciphertext.iter().skip(x_coordinate_len).enumerate() {
            message[i] = ciphertext_byte.wrapping_sub(sponge_bytes[i]);
        }

        Ok(message)
    }

    fn parameters(&self) -> &<Self as EncryptionScheme>::Parameters {
        &self.generator
    }

    fn private_key_size_in_bits() -> usize {
        Self::PrivateKey::size_in_bits()
    }
}

impl<TE: TwistedEdwardsParameters> From<TEAffine<TE>> for ECIESPoseidonEncryption<TE> {
    fn from(generator: TEAffine<TE>) -> Self {
        Self { generator }
    }
}

impl<TE: TwistedEdwardsParameters> ToBytes for ECIESPoseidonEncryption<TE> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.generator.write_le(&mut writer)
    }
}

impl<TE: TwistedEdwardsParameters> FromBytes for ECIESPoseidonEncryption<TE> {
    #[inline]
    fn read_le<R: Read>(reader: R) -> IoResult<Self> {
        let generator = TEAffine::<TE>::read_le(reader)?;
        Ok(Self { generator })
    }
}

impl<TE: TwistedEdwardsParameters> ToConstraintField<TE::BaseField> for ECIESPoseidonEncryption<TE> {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<TE::BaseField>, ConstraintFieldError> {
        Ok(Vec::new())
    }
}
