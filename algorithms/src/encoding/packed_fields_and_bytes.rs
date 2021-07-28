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

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct PackedFieldsAndBytesEncodingScheme<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> ToBytes for PackedFieldsAndBytesEncodingScheme<F> {
    fn write_le<W: Write>(&self, _writer: W) -> IoResult<()> {
        Ok(())
    }
}

impl<F: PrimeField> FromBytes for PackedFieldsAndBytesEncodingScheme<F> {
    fn read_le<R: Read>(_reader: R) -> IoResult<Self> {
        Ok(Self::default())
    }
}

impl<F: PrimeField> From<<Self as EncodingScheme>::Parameters> for PackedFieldsAndBytesEncodingScheme<F> {
    fn from(_: <Self as EncodingScheme>::Parameters) -> Self {
        Self::default()
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PackedFieldsAndBytes<F: PrimeField> {
    pub field_elements: Vec<F>,
    pub remaining_bytes: Vec<u8>,
}

impl<F: PrimeField> ToBytes for PackedFieldsAndBytes<F> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.field_elements.len() as u64).write_le(&mut writer)?;
        for elem in self.field_elements.iter() {
            elem.write_le(&mut writer)?;
        }

        (self.remaining_bytes.len() as u8).write_le(&mut writer)?;
        for byte in self.remaining_bytes.iter() {
            byte.write_le(&mut writer)?;
        }

        Ok(())
    }
}

impl<F: PrimeField> FromBytes for PackedFieldsAndBytes<F> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let field_elements_len = u64::read_le(&mut reader)?;
        let mut field_elements = Vec::with_capacity(field_elements_len as usize);
        for _ in 0..field_elements_len {
            field_elements.push(F::read_le(&mut reader)?);
        }

        let remaining_bytes_len = u8::read_le(&mut reader)?;
        let mut remaining_bytes = Vec::with_capacity(remaining_bytes_len as usize);
        for _ in 0..remaining_bytes_len {
            remaining_bytes.push(u8::read_le(&mut reader)?);
        }

        Ok(Self {
            field_elements,
            remaining_bytes,
        })
    }
}

impl<F: PrimeField> ToConstraintField<F> for PackedFieldsAndBytes<F> {
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        let mut res = self.field_elements.clone();
        if !self.remaining_bytes.is_empty() {
            res.extend_from_slice(&self.remaining_bytes.to_field_elements()?);
        }
        Ok(res)
    }
}

impl<F: PrimeField> EncodingScheme for PackedFieldsAndBytesEncodingScheme<F> {
    type Data = Vec<u8>;
    type EncodedData = PackedFieldsAndBytes<F>;
    type Parameters = ();

    fn setup(_message: &str) -> Self {
        Self::default()
    }

    fn encode(&self, data: &Self::Data) -> Result<Self::EncodedData, EncodingError> {
        // Convert the input into bits.
        let capacity = <F::Parameters as FieldParameters>::CAPACITY as usize;
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
        let cutoff = capacity / 8 * 8;

        let mut field_elements_len = bits.len() / capacity;
        let mut remaining_bits_len = bits.len() % capacity;
        let mut remaining_bytes_len = (remaining_bits_len + 7) / 8;

        if remaining_bits_len > cutoff {
            field_elements_len += 1;
            remaining_bits_len = 0;
            remaining_bytes_len = 0;
        }

        // Pack the field elements part.
        let mut field_elements = Vec::<F>::with_capacity(field_elements_len);
        for chunk in bits[..core::cmp::min(bits.len(), field_elements_len * capacity)].chunks(capacity) {
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

    fn decode(&self, data: &Self::EncodedData) -> Result<Self::Data, EncodingError> {
        // Check if the encoded data is well-formed.
        let capacity = <F::Parameters as FieldParameters>::CAPACITY as usize;
        assert!(data.remaining_bytes.len() <= (capacity + 7) / 8);

        let mut bits = Vec::with_capacity(data.field_elements.len() * capacity + data.remaining_bytes.len() * 8);

        // Unpack the field elements.
        for elem in data.field_elements.iter() {
            let elem_bits = elem.to_repr().to_bits_le();
            bits.extend_from_slice(&elem_bits[..capacity]); // only keep `capacity` bits, discarding the highest bit.
        }

        // Unpack the remaining bytes.
        for byte in data.remaining_bytes.iter() {
            let mut byte = byte.clone();
            for _ in 0..8 {
                bits.push(byte & 1 == 1);
                byte >>= 1;
            }
        }

        // Truncate to bits to a multiply of eight.
        let num_bytes = bits.len() / 8;
        let mut bytes = Vec::with_capacity(num_bytes);
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
