// Copyright (C) 2019-2022 Aleo Systems Inc.
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
    crypto_hash::{hash_to_curve, Poseidon},
    EncryptionScheme,
};
use snarkvm_curves::{
    templates::twisted_edwards_extended::{Affine as TEAffine, Projective},
    AffineCurve,
    ProjectiveCurve,
    TwistedEdwardsParameters,
};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_utilities::{ops::Mul, serialize::*, BitIteratorBE, FromBits, ToBits, Uniform};

use anyhow::{bail, Result};
use itertools::Itertools;
use rand::{CryptoRng, Rng};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ECIESPoseidonEncryption<TE: TwistedEdwardsParameters>
where
    TE::BaseField: PrimeField,
{
    generator: TEAffine<TE>,
    poseidon: Poseidon<TE::BaseField, 4>,
    symmetric_key_commitment_domain: TE::BaseField,
    symmetric_encryption_domain: TE::BaseField,
}

impl<TE: TwistedEdwardsParameters> EncryptionScheme for ECIESPoseidonEncryption<TE>
where
    TE::BaseField: PrimeField,
{
    type CiphertextRandomizer = TE::BaseField;
    type MessageType = TE::BaseField;
    type Parameters = TEAffine<TE>;
    type PrivateKey = TE::ScalarField;
    type PublicKey = TEAffine<TE>;
    type ScalarRandomness = TE::ScalarField;
    type SymmetricKey = TE::BaseField;
    type SymmetricKeyCommitment = TE::BaseField;

    fn setup(message: &str) -> Self {
        let (generator, _, _) = hash_to_curve::<TEAffine<TE>>(message);
        let poseidon = Poseidon::<TE::BaseField, 4>::setup();
        let symmetric_key_commitment_domain = TE::BaseField::from_bytes_le_mod_order(b"AleoSymmetricKeyCommitment0");
        let symmetric_encryption_domain = TE::BaseField::from_bytes_le_mod_order(b"AleoSymmetricEncryption0");

        Self { generator, poseidon, symmetric_key_commitment_domain, symmetric_encryption_domain }
    }

    fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> Self::PrivateKey {
        Self::PrivateKey::rand(rng)
    }

    fn generate_public_key(&self, private_key: &Self::PrivateKey) -> Self::PublicKey {
        self.generator.to_projective().mul(*private_key).to_affine()
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
        let randomness: Self::ScalarRandomness = Uniform::rand(rng);

        // Compute the randomizer := G^r
        let ciphertext_randomizer =
            self.generator.mul_bits(BitIteratorBE::new_without_leading_zeros(randomness.to_repr()));

        // Compute the ECDH value := public_key^r.
        // Note for twisted Edwards curves, only one of (x, y) or (x, -y) is in the prime-order subgroup.
        let symmetric_key = public_key.mul_bits(BitIteratorBE::new_without_leading_zeros(randomness.to_repr()));

        let mut batch = [ciphertext_randomizer, symmetric_key];
        Projective::<TE>::batch_normalization(&mut batch);
        let (ciphertext_randomizer, symmetric_key) =
            (batch[0].to_affine().to_x_coordinate(), batch[1].to_affine().to_x_coordinate());

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
                .to_affine()
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
        self.poseidon.evaluate(&[self.symmetric_key_commitment_domain, *symmetric_key])
    }

    ///
    /// Encode the message bytes into field elements.
    ///
    fn encode_message(message: &[u8]) -> Result<Vec<Self::MessageType>> {
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

        // Pack the bits into field elements.
        Ok(plaintext_bits
            .chunks(capacity)
            .map(|chunk| {
                TE::BaseField::from_repr(<TE::BaseField as PrimeField>::BigInteger::from_bits_le(chunk).unwrap())
                    .unwrap()
            })
            .collect())
    }

    ///
    /// Decode the field elements into bytes.
    ///
    fn decode_message(encoded_message: &[Self::MessageType]) -> Result<Vec<u8>> {
        let capacity = <<TE::BaseField as PrimeField>::Parameters as FieldParameters>::CAPACITY as usize;

        let mut bits = Vec::<bool>::with_capacity(encoded_message.len() * capacity);
        for element in encoded_message.iter() {
            // Only keep `capacity` bits, discarding the highest bit.
            bits.extend_from_slice(&element.to_repr().to_bits_le()[..capacity]);
        }

        // Drop all the ending zeros and the last "1" bit.
        // Note that there must be at least one "1" bit because the last element is not zero.
        loop {
            if let Some(true) = bits.pop() {
                break;
            }
        }

        if bits.len() % 8 != 0 {
            bail!("The number of bits in the packed field elements is not a multiple of 8.")
        }

        // Convert the bits into bytes.
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

    ///
    /// Encrypts the given message, and returns the following:
    ///
    /// ```ignore
    ///     ciphertext := to_bytes_le![C_1, ..., C_n], where C_i := R_i + M_i, and R_i := H_i(G^ar)
    /// ```
    ///
    fn encrypt(&self, symmetric_key: &Self::SymmetricKey, message: &[Self::MessageType]) -> Vec<Self::MessageType> {
        // Obtain random field elements from Poseidon.
        let randomizers =
            self.poseidon.evaluate_many(&[self.symmetric_encryption_domain, *symmetric_key], message.len());

        // Add the random field elements to the plaintext elements.
        message.iter().zip_eq(randomizers).map(|(plaintext, randomizer)| *plaintext + randomizer).collect()
    }

    ///
    /// Decrypts the given ciphertext with the given symmetric key.
    ///
    fn decrypt(&self, symmetric_key: &Self::SymmetricKey, ciphertext: &[Self::MessageType]) -> Vec<Self::MessageType> {
        // Obtain random field elements from Poseidon.
        let randomizers =
            self.poseidon.evaluate_many(&[self.symmetric_encryption_domain, *symmetric_key], ciphertext.len());

        // Subtract the random field elements to the ciphertext elements.
        ciphertext.iter().zip_eq(randomizers).map(|(ciphertext, randomizer)| *ciphertext - randomizer).collect()
    }

    fn parameters(&self) -> &<Self as EncryptionScheme>::Parameters {
        &self.generator
    }
}
