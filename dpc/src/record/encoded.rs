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

use crate::{DPCError, EncodedRecordScheme, Parameters, Payload, Record, RecordScheme};
use snarkvm_algorithms::{
    encoding::Elligator2,
    traits::{CommitmentScheme, CRH},
    EncodingError,
};
use snarkvm_curves::traits::{AffineCurve, MontgomeryParameters, ProjectiveCurve, TwistedEdwardsParameters};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_utilities::{
    from_bits_le_to_bytes_le,
    from_bytes_le_to_bits_le,
    to_bytes_le,
    BigInteger,
    FromBits,
    FromBytes,
    ToBits,
    ToBytes,
};

use itertools::Itertools;
use snarkvm_utilities::io::Cursor;
use std::marker::PhantomData;

/// Encode a base field element bytes to a group representation.
pub fn encode_to_field<F: PrimeField>(x_bytes: &[u8]) -> Result<Vec<F>, DPCError> {
    let capacity = <F::Parameters as FieldParameters>::CAPACITY as usize;

    let mut bits = Vec::<bool>::with_capacity(x_bytes.len() * 8 + 1);
    for byte in x_bytes.iter() {
        let mut byte = byte.clone();
        for _ in 0..8 {
            bits.push(byte & 1 == 1);
            byte >>= 1;
        }
    }
    bits.push(true);
    // The last bit indicates the end of the actual data, which is used in decoding to
    // make sure that the length is correct.

    let mut res = Vec::<F>::with_capacity((bits + 1 + capacity - 1) / capacity);
    for chunk in bits.chunks(capacity).iter() {
        res.push(F::from_repr(F::BigInteger::from_bits_le(chunk)).unwrap());
    }

    Ok(res)
}

/// Decode a group into the byte representation of a base field element.
pub fn decode_from_field<F: PrimeField>(field_elements: &[F]) -> Result<Vec<u8>, DPCError> {
    if field_elements.len() == 0 {
        return Err(DPCError::EncodingError(EncodingError::Message(
            "The encoded record must consist of at least one field element.".to_string(),
        )));
    }
    // There is at least one field element due to the additional true bit.

    let capacity = <F::Parameters as FieldParameters>::CAPACITY as usize;

    let mut bits = Vec::<bool>::with_capacity(field_elements.len() * capacity);
    for elem in field_elements.iter() {
        let elem_bits = elem.to_repr().to_bits_le();
        bits.extend_from_slice(&elem_bits[0..capacity]); // only keep `capacity` bits, discarding the highest bit.
    }

    // Find the last bit of `true`, which should be within the last `CAPACITY` bits.
    // If it does not exist, this is a `DPCError::EncodingError`.
    let mut last_bit_pos = None;
    for i in ((bits.len() - capacity)..(bits.len())).rev() {
        if bits[i] == true {
            last_bit_pos = Some(i);
            break;
        }
    }

    if last_bit_pos.is_none() {
        return Err(DPCError::EncodingError(EncodingError::Message(
            "The encoded record does not end with an expected termination bit.".to_string(),
        )));
    }

    bits.truncate(last_bit_pos.unwrap());
    // This also removes the additional termination bit.

    if (bits.len() % 8 != 0) {
        return Err(DPCError::EncodingError(EncodingError::Message(
            "The number of bits in the encoded record is not a multiply of 8.".to_string(),
        )));
    }
    // Here we do not use assertion since it can cause Rust panicking.

    let mut bytes = Vec::with_capacity(bits.len() / 8);
    for chunk in bits.chunks_exact(8) {
        let mut byte = 0u8;
        for bit in chunk.iter().rev() {
            byte <<= 1;
            byte += bit as u8;
        }
        bytes.push(byte);
    }

    Ok(bytes)
}

pub struct DecodedRecord<C: Parameters> {
    pub value: u64,
    pub payload: Payload,
    pub birth_program_id: Vec<u8>,
    pub death_program_id: Vec<u8>,
    pub serial_number_nonce: <C::SerialNumberNonceCRH as CRH>::Output,
    pub commitment_randomness: <C::RecordCommitmentScheme as CommitmentScheme>::Randomness,
}

pub struct EncodedRecord<C: Parameters> {
    pub(super) encoded_elements: Vec<C::InnerScalarField>,
}

impl<C: Parameters> EncodedRecord<C> {
    pub fn new(encoded_elements: Vec<C::InnerScalarField>) -> Self {
        Self { encoded_elements }
    }
}

impl<C: Parameters> EncodedRecordScheme for EncodedRecord<C> {
    type DecodedRecord = DecodedRecord<C>;
    type Field = C::InnerScalarField;
    type Record = Record<C>;

    /// Records are serialized by
    /// - arranging the following elements in bytes
    /// - converting these bytes into field elements
    ///
    /// Encoded part 1 - [ Serial number nonce ]
    /// Encoded part 2 - [ Commitment randomness ]
    /// Encoded part 3 - [ Birth program id ]
    /// Encoded part 4 - [ Death program id ]
    /// Encoded part 5 - [ Value ]
    /// Encoded part 6 - [ Payload ]
    ///
    fn encode(record: &Self::Record) -> Result<Self, DPCError> {
        let mut bytes = vec![];

        // Serial number nonce
        let serial_number_nonce = record.serial_number_nonce();
        bytes.extend_from_slice(&serial_number_nonce.to_bytes_le()?);

        // Commitment randomness
        let commitment_randomness = record.commitment_randomness();
        bytes.extend_from_slice(&commitment_randomness.to_bytes_le()?);

        // Birth program ID
        let birth_program_id = record.birth_program_id();
        bytes.extend_from_slice(&birth_program_id.to_bytes_le()?);

        // Death program ID
        let death_program_id = record.death_program_id();
        bytes.extend_from_slice(&death_program_id.to_bytes_le()?);

        // Value
        let value = record.value();
        bytes.extend_from_slice(&value.to_bytes_le()?);

        // Payload
        let payload = record.payload();
        bytes.extend_from_slice(&payload.to_bytes_le()?);

        // Pack as field elements
        Ok(Self::new(encode_to_field(&bytes)?))
    }

    /// Decode and return the record components.
    fn decode(&self) -> Result<Self::DecodedRecord, DPCError> {
        let bits = decode_from_field(&self.encoded_elements)?;

        let mut cursor = Cursor::new(bits);

        // Serial number nonce
        let serial_number_nonce = <C::SerialNumberNonceCRH as CRH>::Output::read_le(&mut cursor)?;

        // Commitment randomness
        let commitment_randomness = <C::RecordCommitmentScheme as CommitmentScheme>::Randomness::read_le(&mut cursor)?;

        let program_id_length = to_bytes_le!(<C::ProgramIDCRH as CRH>::Output::default())?.len();

        // Birth program ID

        // Deserialize birth and death programs

        let (birth_program_id, birth_program_id_sign_high) = &(self.encoded_elements[2], fq_high_bits[2]);
        let birth_program_id_bytes = decode_from_group::<Self::Parameters, Self::Group>(
            birth_program_id.into_affine(),
            *birth_program_id_sign_high,
        )?;

        let (death_program_id, death_program_id_sign_high) = &(self.encoded_elements[3], fq_high_bits[3]);
        let death_program_id_bytes = decode_from_group::<Self::Parameters, Self::Group>(
            death_program_id.into_affine(),
            *death_program_id_sign_high,
        )?;

        let (program_id_remainder, program_id_sign_high) = &(self.encoded_elements[4], fq_high_bits[4]);
        let program_id_remainder_bytes = decode_from_group::<Self::Parameters, Self::Group>(
            program_id_remainder.into_affine(),
            *program_id_sign_high,
        )?;

        let mut birth_program_id_bits = from_bytes_le_to_bits_le(&birth_program_id_bytes)
            .take(Self::DATA_ELEMENT_BITSIZE)
            .collect::<Vec<_>>();
        let mut death_program_id_bits = from_bytes_le_to_bits_le(&death_program_id_bytes)
            .take(Self::DATA_ELEMENT_BITSIZE)
            .collect::<Vec<_>>();

        let mut program_id_remainder_bits = from_bytes_le_to_bits_le(&program_id_remainder_bytes);
        birth_program_id_bits.extend(program_id_remainder_bits.by_ref().take(remainder_size));
        death_program_id_bits.extend(program_id_remainder_bits.take(remainder_size));

        let birth_program_id = from_bits_le_to_bytes_le(&birth_program_id_bits);
        let death_program_id = from_bits_le_to_bytes_le(&death_program_id_bits);

        // Deserialize the value

        let value_start = self.encoded_elements.len();
        let value_end = value_start + (std::mem::size_of_val(&<Self::Record as RecordScheme>::Value::default()) * 8);
        let value: <Self::Record as RecordScheme>::Value =
            FromBytes::read_le(&from_bits_le_to_bytes_le(&final_element_bits[value_start..value_end])[..])?;

        // Deserialize payload

        let mut payload_bits = vec![];
        for (element, fq_high) in self.encoded_elements[5..self.encoded_elements.len() - 1]
            .iter()
            .zip_eq(&fq_high_bits[5..])
        {
            let element_bytes = decode_from_group::<Self::Parameters, Self::Group>(element.into_affine(), *fq_high)?;
            payload_bits.extend(from_bytes_le_to_bits_le(&element_bytes).take(Self::PAYLOAD_ELEMENT_BITSIZE));
        }
        payload_bits.extend_from_slice(&final_element_bits[value_end..]);

        let payload = Payload::read_le(&from_bits_le_to_bytes_le(&payload_bits)[..])?;

        Ok(DecodedRecord {
            value,
            payload,
            birth_program_id,
            death_program_id,
            serial_number_nonce,
            commitment_randomness,
        })
    }
}
