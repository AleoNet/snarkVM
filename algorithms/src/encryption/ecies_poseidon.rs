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
        // Keep trying until finding a key that is within the field's capacity bit limits.
        loop {
            let key = Self::PrivateKey::rand(rng);
            let bits = key.to_bits_le();

            for bit in bits
                .iter()
                .skip(<TE::ScalarField as PrimeField>::Parameters::CAPACITY as usize)
            {
                if *bit == true {
                    continue;
                }
            }

            return key;
        }
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

        // Squeeze two elements for the polynomial MAC.
        // The polynomial MAC is defined in https://eprint.iacr.org/2021/318.
        let (polymac_y, polymac_z) = {
            let polymac_elems = sponge.squeeze_field_elements(2);
            (polymac_elems[0], polymac_elems[1])
        };

        // Convert the message into bits.
        let mut bits = Vec::<bool>::with_capacity(message.len() * 8 + 1);
        for byte in message.iter() {
            let mut byte = byte.clone();
            for _ in 0..8 {
                bits.push(byte & 1 == 1);
                byte >>= 1;
            }
        }
        bits.push(true);
        // The last bit indicates the end of the actual data, which is used in decoding to
        // make sure that the length is correct.

        // Pack the bits into field elements.
        let capacity = <<TE::BaseField as PrimeField>::Parameters as FieldParameters>::CAPACITY as usize;
        let mut res = Vec::with_capacity((bits.len() + capacity - 1) / capacity + 1);
        for chunk in bits.chunks(capacity) {
            res.push(TE::BaseField::from_repr(<TE::BaseField as PrimeField>::BigInteger::from_bits_le(chunk)).unwrap());
        }

        // Compute the polynomial MAC and put it into the `res` array.
        let polymac_val = {
            let mut polymac_val = TE::BaseField::zero();
            let mut cur = polymac_y.clone();

            for elem in res.iter().rev() {
                polymac_val += *elem * &cur;
                cur *= &polymac_y;
            }

            polymac_val += <TE::BaseField as From<u128>>::from(res.len() as u128) * &cur;
            polymac_val += &polymac_z;

            polymac_val
        };
        res.push(polymac_val);

        // Obtain random field elements from Poseidon.
        let sponge_field_elements = sponge.squeeze_field_elements(res.len());

        // Add the random field elements to the packed bits.
        for (i, sponge_field_element) in sponge_field_elements.iter().enumerate() {
            res[i] = res[i] + sponge_field_element;
        }

        // Put the bytes of the x coordinate of the randomness group element
        // into the beginning of the ciphertext.
        let random_element = self
            .generator
            .into_projective()
            .mul((*randomness).clone())
            .into_affine()
            .to_x_coordinate();

        Ok([random_element.to_bytes_le()?, res.to_bytes_le()?].concat())
    }

    fn decrypt(
        &self,
        private_key: &<Self as EncryptionScheme>::PrivateKey,
        ciphertext: &[u8],
    ) -> Result<Vec<u8>, EncryptionError> {
        // Ensure that the private key follows the format requirement.
        {
            let bits = private_key.to_bits_le();
            for bit in bits
                .iter()
                .skip(<TE::ScalarField as PrimeField>::Parameters::CAPACITY as usize)
            {
                if *bit == true {
                    return Err(EncryptionError::InvalidPrivateKey);
                }
            }
        }

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
        let params =
            <TE::BaseField as PoseidonDefaultParametersField>::get_default_poseidon_parameters(4, false).unwrap();
        let mut sponge = PoseidonSponge::<TE::BaseField>::new(&params);
        sponge.absorb(&[ecdh_value.x]); // For TE curves, only one of (x, y) and (x, -y) would be on the curve.

        // Squeeze two elements for the polynomial MAC.
        let (polymac_y, polymac_z) = {
            let polymac_elems = sponge.squeeze_field_elements(2);
            (polymac_elems[0], polymac_elems[1])
        };

        // Compute the number of sponge elements needed.
        let num_field_elements = (ciphertext.len() - per_field_element_bytes) / per_field_element_bytes;

        // Obtain random field elements from Poseidon.
        let sponge_field_elements = sponge.squeeze_field_elements(num_field_elements);

        // Subtract the random field elements to the packed bits.
        let mut res_field_elements = Vec::with_capacity(num_field_elements);
        for i in 0..num_field_elements {
            res_field_elements.push(TE::BaseField::from_bytes_le(
                &ciphertext[(per_field_element_bytes + i * per_field_element_bytes)
                    ..(per_field_element_bytes + (i + 1) * per_field_element_bytes)],
            )?);
        }
        for (i, sponge_field_element) in sponge_field_elements.iter().enumerate() {
            res_field_elements[i] = res_field_elements[i] - sponge_field_element;
        }

        // Recompute the polynomial MAC.
        let polymac_val = {
            let mut polymac_val = TE::BaseField::zero();
            let mut cur = polymac_y.clone();

            for elem in res_field_elements.iter().take(num_field_elements - 1).rev() {
                polymac_val += *elem * &cur;
                cur *= &polymac_y;
            }

            polymac_val += <TE::BaseField as From<u128>>::from((num_field_elements - 1) as u128) * &cur;
            polymac_val += &polymac_z;

            polymac_val
        };
        if res_field_elements[num_field_elements - 1] != polymac_val {
            return Err(EncryptionError::MismatchedMAC);
        }

        // drop the polynomial MAC element to simplify the remaining computation.
        res_field_elements.truncate(num_field_elements - 1);

        // Return a decryption error if the polynomial MAC value does not match.

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
