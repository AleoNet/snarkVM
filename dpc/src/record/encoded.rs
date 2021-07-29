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

use crate::{DPCError, Parameters, Payload, Record, RecordScheme};
use snarkvm_algorithms::{
    traits::{CommitmentScheme, CRH},
    EncodingScheme,
};
use snarkvm_utilities::{io::Cursor, to_bytes_le, FromBytes, Read, ToBytes};

pub struct DecodedRecord<C: Parameters> {
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
    pub serial_number_nonce: <C::SerialNumberNonceCRH as CRH>::Output,
    pub commitment_randomness: <C::RecordCommitmentScheme as CommitmentScheme>::Randomness,
    pub birth_program_id: Vec<u8>,
    pub death_program_id: Vec<u8>,
    pub value: u64,
    pub payload: Payload,
}

pub struct EncodedRecord<C: Parameters> {
    pub plaintext: <C::RecordEncodingScheme as EncodingScheme>::EncodedData,
}

impl<C: Parameters> EncodedRecord<C> {
    pub fn new(plaintext: <C::RecordEncodingScheme as EncodingScheme>::EncodedData) -> Self {
        Self { plaintext }
    }

    pub fn encode(record: &Record<C>) -> Result<Self, DPCError> {
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

        let encoded_record = C::RecordEncodingScheme::encode(&bytes)?;

        // Pack as field elements
        Ok(Self::new(encoded_record))
    }

    /// Decode and return the record components.
    pub fn decode(&self) -> Result<DecodedRecord<C>, DPCError> {
        let bits = C::RecordEncodingScheme::decode(&self.plaintext)?;

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

        Ok(DecodedRecord::<C> {
            value,
            payload,
            birth_program_id,
            death_program_id,
            serial_number_nonce,
            commitment_randomness,
        })
    }
}
