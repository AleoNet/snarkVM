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

use super::*;

impl<A: Aleo> ToFields for Ciphertext<A> {
    type Field = Field<A>;

    /// Returns this ciphertext as a list of field elements.
    fn to_fields(&self) -> Vec<Self::Field> {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match self.0.len() <= A::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => self.0.clone(),
            false => A::halt("Ciphertext exceeds maximum allowed size"),
        }
    }
}
