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
    crypto_hash::{CryptographicSponge, PoseidonDefaultParametersField, PoseidonParameters, PoseidonSponge},
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
use snarkvm_fields::{ConstraintFieldError, FieldParameters, PrimeField, ToConstraintField, Zero};
use snarkvm_utilities::{
    io::Result as IoResult,
    ops::Mul,
    serialize::*,
    FromBits,
    FromBytes,
    Read,
    SerializationError,
    ToBits,
    ToBytes,
    UniformRand,
    Write,
};

use itertools::Itertools;
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

impl<TE: TwistedEdwardsParameters> EncryptionScheme for ECIESPoseidonEncryption<TE>
where
    TE::BaseField: PoseidonDefaultParametersField,
{
    type Parameters = TEAffine<TE>;
    type PrivateKey = TE::ScalarField;
    type PublicKey = TEAffine<TE>;
    type Randomness = TE::ScalarField;

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

    fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> <Self as EncryptionScheme>::PrivateKey {
        Self::PrivateKey::rand(rng)
    }

    fn generate_public_key(
        &self,
        private_key: &<Self as EncryptionScheme>::PrivateKey,
    ) -> <Self as EncryptionScheme>::PublicKey {
        self.generator.into_projective().mul(*private_key).into_affine()
    }

    fn generate_randomness<R: Rng + CryptoRng>(&self, rng: &mut R) -> Self::Randomness {
        Self::Randomness::rand(rng)
    }

    fn encrypt(
        &self,
        public_key: &<Self as EncryptionScheme>::PublicKey,
        randomness: &Self::Randomness,
        message: &[u8],
    ) -> Result<Vec<u8>, EncryptionError> {
        // Compute the randomizer := G^r
        let randomizer = self
            .generator
            .into_projective()
            .mul(*randomness)
            .into_affine()
            .to_x_coordinate();

        // Compute the ECDH value := public_key^r.
        // Note for twisted Edwards curves, only one of (x, y) or (x, -y) is on the curve.
        let ecdh_value = public_key
            .into_projective()
            .mul(*randomness)
            .into_affine()
            .to_x_coordinate();

        // Prepare the Poseidon sponge.
        let mut sponge = PoseidonSponge::new(&self.poseidon_parameters);
        sponge.absorb(&[ecdh_value]);

        // Squeeze one element for the commitment randomness.
        let commitment_randomness = sponge.squeeze_field_elements(1)[0];

        // Add a commitment to the public key.
        let public_key_commitment = {
            let mut sponge = PoseidonSponge::new(&self.poseidon_parameters);
            sponge.absorb(&[commitment_randomness, public_key.x]);
            sponge.squeeze_field_elements(1)[0]
        };

        // Convert the message into bits.
        let mut plaintext_bits = Vec::<bool>::with_capacity(message.len() * 8 + 1);
        for byte in message.iter() {
            let mut byte = byte.clone();
            for _ in 0..8 {
                plaintext_bits.push(byte & 1 == 1);
                byte >>= 1;
            }
        }
        // The final bit serves as a terminus indicator,
        // and is used during decryption to ensure the length is correct.
        plaintext_bits.push(true);

        // Determine the number of ciphertext elements.
        let capacity = <<TE::BaseField as PrimeField>::Parameters as FieldParameters>::CAPACITY as usize;
        let num_ciphertext_elements = (plaintext_bits.len() + capacity - 1) / capacity;

        // Obtain random field elements from Poseidon.
        let sponge_randomizers = sponge.squeeze_field_elements(num_ciphertext_elements);
        assert_eq!(sponge_randomizers.len(), num_ciphertext_elements);

        // Pack the bits into field elements and add the random field elements to the packed bits.
        let ciphertext = plaintext_bits
            .chunks(capacity)
            .zip_eq(sponge_randomizers.iter())
            .flat_map(|(chunk, sponge_randomizer)| {
                let plaintext_element =
                    TE::BaseField::from_repr(<TE::BaseField as PrimeField>::BigInteger::from_bits_le(chunk)).unwrap();
                (plaintext_element + sponge_randomizer).to_bytes_le().unwrap()
            })
            .collect();

        // Combine the randomizer, public key commitment, and ciphertext elements.
        Ok([
            randomizer.to_bytes_le()?,
            public_key_commitment.to_bytes_le()?,
            ciphertext,
        ]
        .concat())
    }

    fn decrypt(
        &self,
        private_key: &<Self as EncryptionScheme>::PrivateKey,
        ciphertext: &[u8],
    ) -> Result<Vec<u8>, EncryptionError> {
        let per_field_element_bytes = TE::BaseField::zero().to_bytes_le()?.len();
        assert!(ciphertext.len() >= per_field_element_bytes);

        // Recover the randomness group element.
        let random_elem_x = TE::BaseField::from_bytes_le(&ciphertext[..per_field_element_bytes])?;
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
        let mut sponge = PoseidonSponge::new(&self.poseidon_parameters);
        sponge.absorb(&[ecdh_value.x]); // For TE curves, only one of (x, y) and (x, -y) would be on the curve.

        // Squeeze one element for the commitment randomness.
        let commitment_randomness = sponge.squeeze_field_elements(1)[0];

        // Add a commitment to the public key.
        let public_key_commitment = {
            let mut sponge = PoseidonSponge::new(&self.poseidon_parameters);
            let public_key = self.generate_public_key(&private_key);
            sponge.absorb(&[commitment_randomness, public_key.x]);
            sponge.squeeze_field_elements(1)[0]
        };
        let given_public_key_commitment =
            TE::BaseField::from_bytes_le(&ciphertext[per_field_element_bytes..2 * per_field_element_bytes])?;
        if given_public_key_commitment != public_key_commitment {
            return Err(EncryptionError::MismatchingAddress);
        }

        // Compute the number of sponge elements needed.
        let num_field_elements = (ciphertext.len() - 2 * per_field_element_bytes) / per_field_element_bytes;

        // Obtain random field elements from Poseidon.
        let sponge_field_elements = sponge.squeeze_field_elements(num_field_elements);

        // Subtract the random field elements to the packed bits.
        let mut res_field_elements = Vec::with_capacity(num_field_elements);
        for i in 0..num_field_elements {
            res_field_elements.push(TE::BaseField::from_bytes_le(
                &ciphertext[(2 * per_field_element_bytes + i * per_field_element_bytes)
                    ..(2 * per_field_element_bytes + (i + 1) * per_field_element_bytes)],
            )?);
        }
        for (i, sponge_field_element) in sponge_field_elements.iter().enumerate() {
            res_field_elements[i] = res_field_elements[i] - sponge_field_element;
        }

        // Unpack the packed bits.
        if res_field_elements.is_empty() {
            return Err(EncryptionError::Message(
                "The packed field elements must consist of at least one field element.".to_string(),
            )
            .into());
        }
        if res_field_elements.last().unwrap().is_zero() {
            return Err(EncryptionError::Message(
                "The packed field elements must end with a non-zero element.".to_string(),
            )
            .into());
        }

        let capacity = <<TE::BaseField as PrimeField>::Parameters as FieldParameters>::CAPACITY as usize;

        let mut bits = Vec::<bool>::with_capacity(res_field_elements.len() * capacity);
        for elem in res_field_elements.iter() {
            let elem_bits = elem.to_repr().to_bits_le();
            bits.extend_from_slice(&elem_bits[..capacity]); // only keep `capacity` bits, discarding the highest bit.
        }

        // Drop all the ending zeros and the last "1" bit.
        //
        // Note that there must be at least one "1" bit because the last element is not zero.
        loop {
            if let Some(true) = bits.pop() {
                break;
            }
        }

        if bits.len() % 8 != 0 {
            return Err(EncryptionError::Message(
                "The number of bits in the packed field elements is not a multiple of 8.".to_string(),
            )
            .into());
        }
        // Here we do not use assertion since it can cause Rust panicking.

        let mut message = Vec::with_capacity(bits.len() / 8);
        for chunk in bits.chunks_exact(8) {
            let mut byte = 0u8;
            for bit in chunk.iter().rev() {
                byte <<= 1;
                byte += *bit as u8;
            }
            message.push(byte);
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
        let generator = TEAffine::<TE>::read_le(reader)?;
        Ok(Self::from(generator))
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
