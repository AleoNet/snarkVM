// Copyright 2024 Aleo Network Foundation
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

use super::*;

impl<A: Aleo> ToFields for Record<A, Plaintext<A>> {
    type Field = Field<A>;

    /// Returns this record as a list of field elements.
    fn to_fields(&self) -> Vec<Self::Field> {
        // Encode the data as little-endian bits.
        let mut bits_le = self.to_bits_le();
        // Adds one final bit to the data, to serve as a terminus indicator.
        // During decryption, this final bit ensures we've reached the end.
        bits_le.push(Boolean::constant(true));
        // Pack the bits into field elements.
        let fields = bits_le.chunks(A::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect::<Vec<_>>();
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match fields.len() <= A::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => fields,
            false => A::halt("Record<Plaintext> exceeds maximum allowed size"),
        }
    }
}

impl<A: Aleo> ToFields for Record<A, Ciphertext<A>> {
    type Field = Field<A>;

    /// Returns this record as a list of field elements.
    fn to_fields(&self) -> Vec<Self::Field> {
        // Encode the data as little-endian bits.
        let mut bits_le = self.to_bits_le();
        // Adds one final bit to the data, to serve as a terminus indicator.
        // During decryption, this final bit ensures we've reached the end.
        bits_le.push(Boolean::constant(true));
        // Pack the bits into field elements.
        let fields = bits_le.chunks(A::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect::<Vec<_>>();
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match fields.len() <= A::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => fields,
            false => A::halt("Record<Ciphertext> exceeds maximum allowed size"),
        }
    }
}
