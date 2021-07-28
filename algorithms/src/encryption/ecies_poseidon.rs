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
    encoding::PackedFieldsAndBytes,
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
use snarkvm_fields::{ConstraintFieldError, PrimeField, ToConstraintField};
use snarkvm_utilities::{
    io::Result as IoResult,
    ops::Mul,
    serialize::*,
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
    type CipherText = PackedFieldsAndBytes<TE::BaseField>;
    type Parameters = TEAffine<TE>;
    type PlainText = PackedFieldsAndBytes<TE::BaseField>;
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
        message: &Self::PlainText,
    ) -> Result<Self::CipherText, EncryptionError> {
        // Compute the ECDH value.
        let ecdh_value = public_key.0.into_projective().mul((*randomness).clone()).into_affine();

        // Prepare the Poseidon sponge.
        let params =
            <TE::BaseField as PoseidonDefaultParametersField>::get_default_poseidon_parameters(4, false).unwrap();
        let mut sponge = PoseidonSponge::<TE::BaseField>::new(&params);
        sponge.absorb(&[ecdh_value.x]); // For TE curves, only one of (x, y) and (x, -y) would be on the curve.

        // Encrypt the field elements part by adding the field-F pads directly.
        let mut field_elements = sponge.squeeze_field_elements(message.field_elements.len());
        for (i, elem) in message.field_elements.iter().enumerate() {
            field_elements[i] += elem;
        }

        // Put the x coordinate of the randomness group element into the end of the field elements array.
        field_elements.push(
            self.generator
                .into_projective()
                .mul((*randomness).clone())
                .into_affine()
                .to_x_coordinate(),
        );

        // Encrypt the remaining bytes by first truncating the field-F part into bytes and performing a wrapping addition one by one.
        let remaining_bytes = if message.remaining_bytes.is_empty() {
            vec![]
            // avoid unnecessary call to the sponge
        } else {
            let mut remaining_bytes = message.remaining_bytes.clone();
            let sponge_bytes = sponge.squeeze_field_elements(1).first().unwrap().to_bytes_le()?;
            for (i, elem) in sponge_bytes.iter().take(remaining_bytes.len()).enumerate() {
                remaining_bytes[i] = remaining_bytes[i].wrapping_add(*elem);
            }
            remaining_bytes
        };

        Ok(Self::CipherText {
            field_elements,
            remaining_bytes,
        })
    }

    fn decrypt(
        &self,
        private_key: &<Self as EncryptionScheme>::PrivateKey,
        ciphertext: &Self::CipherText,
    ) -> Result<Self::PlainText, EncryptionError> {
        assert!(ciphertext.field_elements.len() >= 1);

        // Recover the randomness group element.
        let random_elem_x = ciphertext.field_elements.last().unwrap().clone();
        let random_elem = {
            let mut first = TEAffine::<TE>::from_x_coordinate(random_elem_x.clone(), true);
            if first.is_some() && !first.unwrap().is_in_correct_subgroup_assuming_on_curve() {
                first = None;
            }
            let mut second = TEAffine::<TE>::from_x_coordinate(random_elem_x, false);
            if second.is_some() && !second.unwrap().is_in_correct_subgroup_assuming_on_curve() {
                second = None;
            }
            first.or(second).unwrap()
        };

        // Compute the ECDH value
        let ecdh_value = random_elem.into_projective().mul((*private_key).clone()).into_affine();

        // Prepare the Poseidon sponge.
        let params =
            <TE::BaseField as PoseidonDefaultParametersField>::get_default_poseidon_parameters(4, false).unwrap();
        let mut sponge = PoseidonSponge::<TE::BaseField>::new(&params);
        sponge.absorb(&[ecdh_value.x]); // For TE curves, only one of (x, y) and (x, -y) would be on the curve.

        // Decrypt the field elements part.
        let field_elements_len = ciphertext.field_elements.len() - 1;
        let mut field_elements = sponge.squeeze_field_elements(field_elements_len);
        for (i, elem) in ciphertext.field_elements.iter().take(field_elements_len).enumerate() {
            field_elements[i] = *elem - field_elements[i];
        }

        // Decrypt the remaining bytes part.
        let remaining_bytes = if ciphertext.remaining_bytes.is_empty() {
            vec![]
            // avoid unnecessary call to the sponge
        } else {
            let mut remaining_bytes = ciphertext.remaining_bytes.clone();
            let sponge_bytes = sponge.squeeze_field_elements(1).first().unwrap().to_bytes_le()?;
            for (i, elem) in sponge_bytes.iter().take(remaining_bytes.len()).enumerate() {
                remaining_bytes[i] = remaining_bytes[i].wrapping_sub(*elem);
            }
            remaining_bytes
        };

        Ok(Self::CipherText {
            field_elements,
            remaining_bytes,
        })
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
