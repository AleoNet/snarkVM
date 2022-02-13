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
    FromBits,
    FromBytes,
    Read,
    ToBits,
    ToBytes,
    UniformRand,
    Write,
};

use itertools::Itertools;
use rand::{CryptoRng, Rng};
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
    generator: TEAffine<TE>,
    poseidon_parameters: Arc<PoseidonParameters<TE::BaseField, 4, 1>>,
    symmetric_key_commitment_domain: TE::BaseField,
    symmetric_encryption_domain: TE::BaseField,
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
    type SymmetricKeyCommitment = TE::BaseField;

    fn setup(message: &str) -> Self {
        let (generator, _, _) = hash_to_curve::<TEAffine<TE>>(message);
        Self::from(generator)
    }

    fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> Self::PrivateKey {
        Self::PrivateKey::rand(rng)
    }

    fn generate_public_key(&self, private_key: &Self::PrivateKey) -> Self::PublicKey {
        self.generator.into_projective().mul(*private_key).into_affine()
    }

    ///
    /// Given an RNG, returns the following:
    ///
    /// ```ignore
    ///                  randomness := r
    ///       ciphertext_randomizer := G^r
    ///               symmetric_key := public_key^r == G^ar
    /// ```
    ///
    fn generate_asymmetric_key<R: Rng + CryptoRng>(
        &self,
        public_key: &Self::PublicKey,
        rng: &mut R,
    ) -> (Self::ScalarRandomness, Self::CiphertextRandomizer, Self::SymmetricKey) {
        // Sample randomness.
        let randomness: Self::ScalarRandomness = UniformRand::rand(rng);

        // Compute the randomizer := G^r
        let ciphertext_randomizer =
            self.generator.mul_bits(BitIteratorBE::new_without_leading_zeros(randomness.to_repr()));

        // Compute the ECDH value := public_key^r.
        // Note for twisted Edwards curves, only one of (x, y) or (x, -y) is in the prime-order subgroup.
        let symmetric_key = public_key.mul_bits(BitIteratorBE::new_without_leading_zeros(randomness.to_repr()));

        let mut batch = [ciphertext_randomizer, symmetric_key];
        Projective::<TE>::batch_normalization(&mut batch);
        let (ciphertext_randomizer, symmetric_key) =
            (batch[0].into_affine().to_x_coordinate(), batch[1].into_affine().to_x_coordinate());

        (randomness, ciphertext_randomizer, symmetric_key)
    }

    ///
    /// Given the private key and ciphertext randomizer, return the following:
    ///
    /// ```ignore
    ///    symmetric_key := public_key^r == (G^r)^private_key
    /// ```
    ///
    fn generate_symmetric_key(
        &self,
        private_key: &<Self as EncryptionScheme>::PrivateKey,
        ciphertext_randomizer: Self::CiphertextRandomizer,
    ) -> Option<Self::SymmetricKey> {
        // Recover the ciphertext randomizer group element.
        let mut randomizer = None;

        if let Some(element) = TEAffine::<TE>::from_x_coordinate(ciphertext_randomizer, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                randomizer = Some(element);
            }
        }
        if randomizer.is_none() {
            if let Some(element) = TEAffine::<TE>::from_x_coordinate(ciphertext_randomizer, false) {
                if element.is_in_correct_subgroup_assuming_on_curve() {
                    randomizer = Some(element);
                }
            }
        }

        randomizer.map(|randomizer| {
            randomizer
                .mul_bits(BitIteratorBE::new_without_leading_zeros(private_key.to_repr()))
                .into_affine()
                .to_x_coordinate()
        })
    }

    ///
    /// Given the symmetric key, return the following:
    ///
    /// ```ignore
    ///    symmetric_key_commitment := H(public_key^r) == H((G^r)^private_key)
    /// ```
    ///
    fn generate_symmetric_key_commitment(&self, symmetric_key: &Self::SymmetricKey) -> Self::SymmetricKeyCommitment {
        // Compute the symmetric key commitment.
        let mut sponge = PoseidonSponge::with_parameters(&self.poseidon_parameters);
        sponge.absorb(&[self.symmetric_key_commitment_domain, *symmetric_key]);
        sponge.squeeze_field_elements(1)[0]
    }

    ///
    /// Encrypts the given message, and returns the following:
    ///
    /// ```ignore
    ///     ciphertext := to_bytes_le![C_1, ..., C_n], where C_i := R_i + M_i, and R_i := H_i(G^ar)
    /// ```
    ///
    fn encrypt(&self, symmetric_key: &Self::SymmetricKey, message: &[u8]) -> Result<Vec<u8>, EncryptionError> {
        // Initialize the sponge state.
        let mut sponge = PoseidonSponge::with_parameters(&self.poseidon_parameters);
        sponge.absorb(&[self.symmetric_encryption_domain, *symmetric_key]);

        // Convert the message into bits.
        let mut plaintext_bits = Vec::<bool>::with_capacity(message.len() * 8 + 1);
        for byte in message.iter() {
            let mut byte = *byte;
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

        Ok(ciphertext)
    }

    ///
    /// Decrypts the given ciphertext with the given symmetric key.
    ///
    fn decrypt(&self, symmetric_key: &Self::SymmetricKey, ciphertext: &[u8]) -> Result<Vec<u8>, EncryptionError> {
        // Initialize sponge state.
        let mut sponge = PoseidonSponge::with_parameters(&self.poseidon_parameters);
        sponge.absorb(&[self.symmetric_encryption_domain, *symmetric_key]);

        let per_field_element_bytes = TE::BaseField::zero().to_bytes_le()?.len();
        assert!(ciphertext.len() >= per_field_element_bytes);

        // Compute the number of sponge elements needed.
        let num_field_elements = ciphertext.len() / per_field_element_bytes;

        // Obtain random field elements from Poseidon.
        let sponge_randomizers = sponge.squeeze_field_elements(num_field_elements);

        // Subtract the random field elements to the packed bits.
        let mut plaintext_elements = Vec::with_capacity(num_field_elements);
        for i in 0..num_field_elements {
            plaintext_elements.push(TE::BaseField::from_bytes_le(
                &ciphertext[(i * per_field_element_bytes)..((i + 1) * per_field_element_bytes)],
            )?);
        }
        for (i, sponge_randomizer) in sponge_randomizers.iter().enumerate() {
            plaintext_elements[i] -= sponge_randomizer;
        }

        // Unpack the packed bits.
        if plaintext_elements.is_empty() {
            return Err(EncryptionError::Message(
                "The packed field elements must consist of at least one field element.".to_string(),
            ));
        }
        if plaintext_elements.last().unwrap().is_zero() {
            return Err(EncryptionError::Message(
                "The packed field elements must end with a non-zero element.".to_string(),
            ));
        }

        let capacity = <<TE::BaseField as PrimeField>::Parameters as FieldParameters>::CAPACITY as usize;

        let mut bits = Vec::<bool>::with_capacity(plaintext_elements.len() * capacity);
        for elem in plaintext_elements.iter() {
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
            ));
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
        let symmetric_key_commitment_domain = TE::BaseField::from_bytes_le_mod_order(b"AleoSymmetricKeyCommitment0");
        let symmetric_encryption_domain = TE::BaseField::from_bytes_le_mod_order(b"AleoSymmetricEncryption0");

        Self { generator, poseidon_parameters, symmetric_key_commitment_domain, symmetric_encryption_domain }
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
