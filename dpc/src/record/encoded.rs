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
    traits::{CommitmentScheme, CRH},
    EncodingError,
};
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_utilities::{io::Cursor, to_bytes_le, FromBits, FromBytes, Read, ToBits, ToBytes};

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

    let mut res = Vec::<F>::with_capacity((bits.len() + capacity - 1) / capacity);
    for chunk in bits.chunks(capacity) {
        res.push(F::from_repr(F::BigInteger::from_bits_le(chunk)).unwrap());
    }

    Ok(res)
}

/// Decode a group into the byte representation of a base field element.
pub fn decode_from_field<F: PrimeField>(field_elements: &[F]) -> Result<Vec<u8>, DPCError> {
    if field_elements.is_empty() {
        return Err(EncodingError::Message(
            "The encoded record must consist of at least one field element.".to_string(),
        )
        .into());
    }
    if field_elements.last().unwrap().is_zero() {
        return Err(EncodingError::Message("The encoded record must end with a non-zero element.".to_string()).into());
    }
    // There is at least one field element due to the additional true bit.

    let capacity = <F::Parameters as FieldParameters>::CAPACITY as usize;

    let mut bits = Vec::<bool>::with_capacity(field_elements.len() * capacity);
    for elem in field_elements.iter() {
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
        return Err(EncodingError::Message(
            "The number of bits in the encoded record is not a multiply of 8.".to_string(),
        )
        .into());
    }
    // Here we do not use assertion since it can cause Rust panicking.

    let mut bytes = Vec::with_capacity(bits.len() / 8);
    for chunk in bits.chunks_exact(8) {
        let mut byte = 0u8;
        for bit in chunk.iter().rev() {
            byte <<= 1;
            byte += *bit as u8;
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
    pub encoded_elements: Vec<C::InnerScalarField>,
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

        // Birth program ID and death program ID
        let program_id_length = to_bytes_le!(<C::ProgramIDCRH as CRH>::Output::default())?.len();
        let birth_program_id = {
            let mut program_id = vec![0u8; program_id_length];
            cursor.read_exact(&mut program_id)?;
            program_id
        };
        let death_program_id = {
            let mut program_id = vec![0u8; program_id_length];
            cursor.read_exact(&mut program_id)?;
            program_id
        };

        // Value
        let value = u64::read_le(&mut cursor)?;

        // Payload
        let payload = Payload::read_le(&mut cursor)?;

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
