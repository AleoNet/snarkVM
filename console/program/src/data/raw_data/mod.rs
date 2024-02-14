// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod bytes;
mod equal;
mod from_bits;
mod from_fields;
mod parse;
mod serialize;
mod size_in_fields;
mod to_bits;
mod to_fields;

use snarkvm_console_network::prelude::*;
use snarkvm_console_types::{Boolean, Field};
use snarkvm_utilities::{bits_from_bytes_le, bytes_from_bits_le};

use core::ops::Deref;

#[derive(Clone)]
pub struct Data<N: Network>(Vec<Field<N>>);

impl<N: Network> Data<N> {
    // TODO (@d0cd) Should these methods be the default implementations to `FromBytes` and `ToBytes`?
    //  They do have some more overhead, and seem to be unnecessary when sending over the wire.
    /// Initializes a new `Data` object from a collection of little-endian bytes.
    #[inline]
    pub fn encode_from_bytes_le(bytes_le: &[u8]) -> Result<Self> {
        let mut bits_le = bits_from_bytes_le(bytes_le).collect::<Vec<_>>();
        // Adds one final bit to the data, to serve as a terminus indicator.
        // During decryption, this final bit ensures we've reached the end.
        bits_le.push(true);
        // Pack the bits into field elements.
        let fields = bits_le
            .chunks(Field::<N>::size_in_data_bits())
            .map(Field::<N>::from_bits_le)
            .collect::<Result<Vec<_>>>()?;
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match fields.len() <= N::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => Ok(Self(fields)),
            false => bail!("Data exceeds maximum allowed size"),
        }
    }

    /// Decodes this `Data` as a collection of little-endian bytes.
    #[inline]
    pub fn decode_as_bytes_le(&self) -> Result<Vec<u8>> {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        if self.len() > N::MAX_DATA_SIZE_IN_FIELDS as usize {
            bail!("Plaintext exceeds maximum allowed size")
        }

        // Unpack the field elements into little-endian bits, and reverse the list for popping the terminus bit off.
        let mut bits_le =
            (*self).iter().flat_map(|field| field.to_bits_le().into_iter().take(Field::<N>::size_in_data_bits())).rev();
        // Remove the terminus bit that was added during encoding.
        for boolean in bits_le.by_ref() {
            // Drop all extraneous `0` bits, in addition to the final `1` bit.
            if boolean {
                // This case will always be reached, since the terminus bit is always `1`.
                break;
            }
        }
        // Reverse the bits back and recover the data from the bits.
        Ok(bytes_from_bits_le(&bits_le.rev().collect::<Vec<_>>()))
    }
}

impl<N: Network> Deref for Data<N> {
    type Target = [Field<N>];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
