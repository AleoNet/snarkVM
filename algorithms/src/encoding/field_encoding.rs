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

use crate::{EncodingError, EncodingScheme};
use snarkvm_fields::{ConstraintFieldError, FieldParameters, PrimeField};
use snarkvm_r1cs::ToConstraintField;
use snarkvm_utilities::{io::Result as IoResult, FromBits, FromBytes, Read, ToBits, ToBytes, Write};

use std::marker::PhantomData;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FieldEncodedData<F: PrimeField> {
    pub field_elements: Vec<F>,
    pub remaining_bytes: Vec<u8>,
}

impl<F: PrimeField> FieldEncodedData<F> {
    /// Returns the number of bits occupied in field elements. It should be noted this is
    /// *not* the number of bits the final field elements occupy in bit size.
    pub fn num_bits(&self) -> usize {
        (self.field_elements.len() * <F::Parameters as FieldParameters>::CAPACITY as usize)
            + (self.remaining_bytes.len() * 8)
    }
}

impl<F: PrimeField> FromBytes for FieldEncodedData<F> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let field_elements_length = u8::read_le(&mut reader)?;
        let mut field_elements = Vec::with_capacity(field_elements_length as usize);
        for _ in 0..field_elements_length {
            field_elements.push(F::read_le(&mut reader)?);
        }

        let remaining_bytes_length = u8::read_le(&mut reader)?;
        let mut remaining_bytes = Vec::with_capacity(remaining_bytes_length as usize);
        for _ in 0..remaining_bytes_length {
            remaining_bytes.push(u8::read_le(&mut reader)?);
        }

        Ok(Self {
            field_elements,
            remaining_bytes,
        })
    }
}

impl<F: PrimeField> ToBytes for FieldEncodedData<F> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.field_elements.len() as u8).write_le(&mut writer)?;
        self.field_elements.write_le(&mut writer)?;
        (self.remaining_bytes.len() as u8).write_le(&mut writer)?;
        self.remaining_bytes.write_le(&mut writer)?;
        Ok(())
    }
}

impl<F: PrimeField> ToConstraintField<F> for FieldEncodedData<F> {
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        Ok(self
            .field_elements
            .clone()
            .into_iter()
            .chain(self.remaining_bytes.to_field_elements()?.into_iter())
            .collect())
    }
}

#[derive(Default, Debug, Clone)]
pub struct FieldEncodingScheme<F: PrimeField>(PhantomData<F>);

impl<F: PrimeField> EncodingScheme for FieldEncodingScheme<F> {
    type Data = Vec<u8>;
    type EncodedData = FieldEncodedData<F>;

    fn encode(data: &Self::Data) -> Result<Self::EncodedData, EncodingError> {
        let field_capacity = <F::Parameters as FieldParameters>::CAPACITY as usize;

        // Convert the input into bits.
        let mut bits = Vec::<bool>::with_capacity(data.len() * 8 + 1);
        for byte in data.iter() {
            let mut byte = byte.clone();
            for _ in 0..8 {
                bits.push(byte & 1 == 1);
                byte >>= 1;
            }
        }

        // Compute the number of remaining bits.
        //
        // We cut off a limit of the remaining bits to capacity / 8 * 8,
        // because Poseidon cannot guarantee so many random bytes.
        let cutoff = field_capacity / 8 * 8;

        let mut field_elements_len = bits.len() / field_capacity;
        let mut remaining_bits_len = bits.len() % field_capacity;
        let mut remaining_bytes_len = (remaining_bits_len + 7) / 8;

        if remaining_bits_len > cutoff {
            field_elements_len += 1;
            remaining_bits_len = 0;
            remaining_bytes_len = 0;
        }

        assert!(
            field_elements_len <= u8::MAX as usize,
            "The packed_fields_and_bytes encoding supports up to 255 field elements and 7 bytes."
        );

        // Pack the field elements part.
        let mut field_elements = Vec::<F>::with_capacity(field_elements_len);
        for chunk in bits[..core::cmp::min(bits.len(), field_elements_len * field_capacity)].chunks(field_capacity) {
            field_elements.push(F::from_repr(F::BigInteger::from_bits_le(chunk)).unwrap());
        }

        // Pack the remaining bytes part.
        let mut remaining_bytes = Vec::with_capacity(remaining_bytes_len);
        for chunk in bits[(bits.len() - remaining_bits_len)..].chunks(8) {
            let mut byte = 0u8;
            for bit in chunk.iter().rev() {
                byte <<= 1;
                byte += *bit as u8;
            }
            remaining_bytes.push(byte);
        }

        Ok(Self::EncodedData {
            field_elements,
            remaining_bytes,
        })
    }

    fn decode(encoded_data: &Self::EncodedData) -> Result<Self::Data, EncodingError> {
        // Check if the encoded data is well-formed.
        let field_capacity = <F::Parameters as FieldParameters>::CAPACITY as usize;
        assert!(encoded_data.remaining_bytes.len() <= (field_capacity + 7) / 8);

        let mut bits = Vec::with_capacity(encoded_data.num_bits());

        // Unpack the field elements.
        for element in &encoded_data.field_elements {
            let element_bits = element.to_repr().to_bits_le();
            bits.extend_from_slice(&element_bits[..field_capacity]); // only keep `capacity` bits, discarding the highest bit.
        }

        // Unpack the remaining bytes.
        for byte in &encoded_data.remaining_bytes {
            let mut byte = byte.clone();
            for _ in 0..8 {
                bits.push(byte & 1 == 1);
                byte >>= 1;
            }
        }

        // Truncate to bits to a multiple of eight.
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
}
