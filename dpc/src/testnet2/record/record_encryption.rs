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
    testnet2::{
        parameters::SystemParameters,
        payload::Payload,
        record::{encoded::*, encrypted_record::*, Record},
        Testnet2Components,
    },
    traits::{DPCComponents, EncodedRecordScheme, RecordScheme},
    Address,
    DPCError,
    ViewKey,
};
use snarkvm_algorithms::{
    encoding::Elligator2,
    traits::{CommitmentScheme, EncryptionScheme, CRH},
};
use snarkvm_curves::traits::{AffineCurve, ModelParameters, ProjectiveCurve};
use snarkvm_fields::One;
use snarkvm_utilities::{bits_to_bytes, bytes_to_bits, to_bytes, FromBytes, ToBytes};

use itertools::Itertools;
use rand::Rng;
use std::marker::PhantomData;

type BaseField<T> = <<T as Testnet2Components>::EncryptionModelParameters as ModelParameters>::BaseField;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Testnet2Components"),
    PartialEq(bound = "C: Testnet2Components"),
    Eq(bound = "C: Testnet2Components")
)]
pub struct RecordEncryptionGadgetComponents<C: Testnet2Components> {
    /// Record field element representations
    pub record_field_elements: Vec<<C::EncryptionModelParameters as ModelParameters>::BaseField>,
    /// Record group element encodings - Represented in (x,y) affine coordinates
    pub record_group_encoding: Vec<(BaseField<C>, BaseField<C>)>,
    /// Record ciphertext selectors - Used for ciphertext compression/decompression
    pub ciphertext_selectors: Vec<bool>,
    /// Record fq high selectors - Used for plaintext serialization/deserialization
    pub fq_high_selectors: Vec<bool>,
    /// Record ciphertext blinding exponents used to encrypt the record
    pub encryption_blinding_exponents: Vec<<C::AccountEncryption as EncryptionScheme>::BlindingExponent>,
}

impl<C: Testnet2Components> Default for RecordEncryptionGadgetComponents<C> {
    fn default() -> Self {
        // TODO (raychu86) Fix the lengths to be generic
        let record_encoding_length = 7;
        let base_field_one = <C::EncryptionModelParameters as ModelParameters>::BaseField::one();
        let base_field_default = <C::EncryptionModelParameters as ModelParameters>::BaseField::default();

        let record_field_elements = vec![base_field_one; record_encoding_length];
        let record_group_encoding = vec![(base_field_default, base_field_default); record_encoding_length];

        let ciphertext_selectors = vec![false; record_encoding_length + 1];
        let fq_high_selectors = vec![false; record_encoding_length];

        let encryption_blinding_exponents =
            vec![<C::AccountEncryption as EncryptionScheme>::BlindingExponent::default(); record_encoding_length];

        Self {
            record_field_elements,
            record_group_encoding,
            ciphertext_selectors,
            fq_high_selectors,
            encryption_blinding_exponents,
        }
    }
}

pub struct RecordEncryption<C: Testnet2Components>(PhantomData<C>);

impl<C: Testnet2Components> RecordEncryption<C> {
    /// Encrypt the given vector of records and returns
    /// 1. Encryption Randomness
    /// 2. Encrypted record
    pub fn encrypt_record<R: Rng>(
        system_parameters: &SystemParameters<C>,
        record: &Record<C>,
        rng: &mut R,
    ) -> Result<
        (
            <<C as DPCComponents>::AccountEncryption as EncryptionScheme>::Randomness,
            EncryptedRecord<C>,
        ),
        DPCError,
    > {
        // Serialize the record into group elements and fq_high bits
        let encoded_record = EncodedRecord::<C, C::EncryptionModelParameters, C::EncryptionGroup>::encode(record)?;
        let final_fq_high_selector = encoded_record.final_sign_high;

        let mut record_plaintexts = Vec::with_capacity(encoded_record.encoded_elements.len());
        for element in encoded_record.encoded_elements.iter() {
            // Construct the plaintext element from the serialized group elements
            // This value will be used in the inner circuit to validate the encryption
            let plaintext_element =
                <<C as DPCComponents>::AccountEncryption as EncryptionScheme>::Text::read(&to_bytes![element]?[..])?;
            record_plaintexts.push(plaintext_element);
        }

        // Encrypt the record plaintext
        let record_public_key = record.owner().into_repr();
        let encryption_randomness = system_parameters
            .account_encryption
            .generate_randomness(record_public_key, rng)?;
        let encrypted_record = C::AccountEncryption::encrypt(
            &system_parameters.account_encryption,
            record_public_key,
            &encryption_randomness,
            &record_plaintexts,
        )?;

        let encrypted_record = EncryptedRecord {
            encrypted_record,
            final_fq_high_selector,
        };

        Ok((encryption_randomness, encrypted_record))
    }

    /// Decrypt and reconstruct the encrypted record
    pub fn decrypt_record(
        system_parameters: &SystemParameters<C>,
        account_view_key: &ViewKey<C>,
        encrypted_record: &EncryptedRecord<C>,
    ) -> Result<Record<C>, DPCError> {
        // Decrypt the encrypted record
        let plaintext_elements = C::AccountEncryption::decrypt(
            &system_parameters.account_encryption,
            &account_view_key.decryption_key,
            &encrypted_record.encrypted_record,
        )?;

        let mut plaintext = Vec::with_capacity(plaintext_elements.len());
        for element in plaintext_elements {
            let plaintext_element = <C as Testnet2Components>::EncryptionGroup::read(&to_bytes![element]?[..])?;

            plaintext.push(plaintext_element);
        }

        // Deserialize the plaintext record into record components
        let encoded_record = EncodedRecord::<
            C,
            <C as Testnet2Components>::EncryptionModelParameters,
            <C as Testnet2Components>::EncryptionGroup,
        >::new(plaintext, encrypted_record.final_fq_high_selector);
        let record_components = encoded_record.decode()?;

        let DecodedRecord {
            serial_number_nonce,
            commitment_randomness,
            birth_program_id,
            death_program_id,
            payload,
            value,
        } = record_components;

        // Construct the record account address

        let owner = Address::from_view_key(&system_parameters.account_encryption, &account_view_key)?;

        // Determine if the record is a dummy

        // TODO (raychu86) Establish `is_dummy` flag properly by checking that the value is 0 and the programs are equivalent to a global dummy
        let dummy_program = birth_program_id.clone();

        let is_dummy = (value == 0)
            && (payload == Payload::default())
            && (death_program_id == dummy_program)
            && (birth_program_id == dummy_program);

        // Calculate record commitment

        let commitment_input = to_bytes![
            owner,
            is_dummy,
            value,
            payload,
            birth_program_id,
            death_program_id,
            serial_number_nonce
        ]?;

        let commitment = C::RecordCommitment::commit(
            &system_parameters.record_commitment,
            &commitment_input,
            &commitment_randomness,
        )?;

        Ok(Record {
            owner,
            is_dummy,
            value,
            payload,
            birth_program_id,
            death_program_id,
            serial_number_nonce,
            commitment_randomness,
            commitment,
            _components: PhantomData,
        })
    }

    /// Returns the encrypted record hash
    /// The hash input is the ciphertext x-coordinates appended with the selector bits
    pub fn encrypted_record_hash(
        system_parameters: &SystemParameters<C>,
        encrypted_record: &EncryptedRecord<C>,
    ) -> Result<<<C as DPCComponents>::EncryptedRecordCRH as CRH>::Output, DPCError> {
        let mut ciphertext_affine_x = Vec::with_capacity(encrypted_record.encrypted_record.len());
        let mut selector_bits = Vec::with_capacity(encrypted_record.encrypted_record.len() + 1);
        for ciphertext_element in &encrypted_record.encrypted_record {
            // Compress the ciphertext element to the affine x coordinate
            let ciphertext_element_affine =
                <C as Testnet2Components>::EncryptionGroup::read(&to_bytes![ciphertext_element]?[..])?.into_affine();
            let ciphertext_x_coordinate = ciphertext_element_affine.to_x_coordinate();

            // Fetch the ciphertext selector bit
            let selector =
                match <<C as Testnet2Components>::EncryptionGroup as ProjectiveCurve>::Affine::from_x_coordinate(
                    ciphertext_x_coordinate,
                    true,
                ) {
                    Some(affine) => ciphertext_element_affine == affine,
                    None => false,
                };

            selector_bits.push(selector);
            ciphertext_affine_x.push(ciphertext_x_coordinate);
        }

        // Concatenate the ciphertext selector bits and the final fq_high selector bit
        selector_bits.push(encrypted_record.final_fq_high_selector);
        let selector_bytes = bits_to_bytes(&selector_bits);

        Ok(system_parameters
            .encrypted_record_crh
            .hash(&to_bytes![ciphertext_affine_x, selector_bytes]?)?)
    }

    /// Returns the intermediate components of the encryption algorithm that the inner SNARK
    /// needs to validate the new record was encrypted correctly
    /// 1. Record field element representations
    /// 2. Record group element encodings - Represented in (x,y) affine coordinates
    /// 3. Record ciphertext selectors - Used for ciphertext compression/decompression
    /// 4. Record fq high selectors - Used for plaintext serialization/deserialization
    /// 5. Record ciphertext blinding exponents used to encrypt the record
    pub fn prepare_encryption_gadget_components(
        system_parameters: &SystemParameters<C>,
        record: &Record<C>,
        encryption_randomness: &<<C as DPCComponents>::AccountEncryption as EncryptionScheme>::Randomness,
    ) -> Result<RecordEncryptionGadgetComponents<C>, DPCError> {
        // Serialize the record into group elements and fq_high bits
        let encoded_record = EncodedRecord::<C, C::EncryptionModelParameters, C::EncryptionGroup>::encode(record)?;
        let num_encoded_elements = encoded_record.encoded_elements.len();
        let final_fq_high_selector = encoded_record.final_sign_high;

        // Extract the fq_bits from the serialized record
        let fq_high_selectors = {
            let final_element = &encoded_record.encoded_elements[num_encoded_elements - 1];
            let final_element_bytes = decode_from_group::<C::EncryptionModelParameters, C::EncryptionGroup>(
                final_element.into_affine(),
                final_fq_high_selector,
            )?;
            let final_element_bits = bytes_to_bits(&final_element_bytes);
            [
                &final_element_bits
                    .skip(1)
                    .take(num_encoded_elements.saturating_sub(1))
                    .collect::<Vec<_>>(),
                &[final_fq_high_selector][..],
            ]
            .concat()
        };

        let mut record_field_elements = Vec::with_capacity(num_encoded_elements);
        let mut record_group_encoding = Vec::with_capacity(num_encoded_elements);
        let mut record_plaintexts = Vec::with_capacity(num_encoded_elements);

        for (i, (element, fq_high)) in encoded_record
            .encoded_elements
            .iter()
            .zip_eq(&fq_high_selectors)
            .enumerate()
        {
            let element_affine = element.into_affine();

            // Decode the field elements from the serialized group element
            // These values will be used in the inner circuit to validate bit packing and serialization
            if i == 0 {
                // Serial number nonce
                let record_field_element =
                    <<C as Testnet2Components>::EncryptionModelParameters as ModelParameters>::BaseField::read(
                        &to_bytes![element]?[..],
                    )?;
                record_field_elements.push(record_field_element);
            } else {
                // Decode the encoded groups into their respective field elements
                let record_field_element = Elligator2::<
                    <C as Testnet2Components>::EncryptionModelParameters,
                    <C as Testnet2Components>::EncryptionGroup,
                >::decode(&element_affine, *fq_high)?;

                record_field_elements.push(record_field_element);
            }

            // Fetch the x and y coordinates of the serialized group elements
            // These values will be used in the inner circuit to validate the Elligator2 encoding
            let x = <<C as Testnet2Components>::EncryptionModelParameters as ModelParameters>::BaseField::read(
                &to_bytes![element_affine.to_x_coordinate()]?[..],
            )?;
            let y = <<C as Testnet2Components>::EncryptionModelParameters as ModelParameters>::BaseField::read(
                &to_bytes![element_affine.to_y_coordinate()]?[..],
            )?;
            record_group_encoding.push((x, y));

            // Construct the plaintext element from the serialized group elements
            // This value will be used in the inner circuit to validate the encryption
            let plaintext_element =
                <<C as DPCComponents>::AccountEncryption as EncryptionScheme>::Text::read(&to_bytes![element]?[..])?;
            record_plaintexts.push(plaintext_element);
        }

        // Encrypt the record plaintext
        let record_public_key = record.owner().into_repr();
        let encryption_blinding_exponents = system_parameters.account_encryption.generate_blinding_exponents(
            record_public_key,
            encryption_randomness,
            record_plaintexts.len(),
        )?;

        let encrypted_record = C::AccountEncryption::encrypt(
            &system_parameters.account_encryption,
            record_public_key,
            &encryption_randomness,
            &record_plaintexts,
        )?;

        // Compute the compressed ciphertext selector bits
        let mut ciphertext_selectors = Vec::with_capacity(encrypted_record.len());
        for ciphertext_element in encrypted_record.iter() {
            // Compress the ciphertext element to the affine x coordinate
            let ciphertext_element_affine =
                <C as Testnet2Components>::EncryptionGroup::read(&to_bytes![ciphertext_element]?[..])?.into_affine();

            // Fetch the ciphertext selector bit
            let selector =
                match <<C as Testnet2Components>::EncryptionGroup as ProjectiveCurve>::Affine::from_x_coordinate(
                    ciphertext_element_affine.to_x_coordinate(),
                    true,
                ) {
                    Some(affine) => ciphertext_element_affine == affine,
                    None => false,
                };

            ciphertext_selectors.push(selector);
        }

        Ok(RecordEncryptionGadgetComponents {
            record_field_elements,
            record_group_encoding,
            ciphertext_selectors,
            fq_high_selectors,
            encryption_blinding_exponents,
        })
    }
}
