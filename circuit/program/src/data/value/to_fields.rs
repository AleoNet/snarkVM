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

impl<A: Aleo> ToFields for Value<A> {
    type Field = Field<A>;

    /// Returns the circuit value as a list of fields.
    #[inline]
    fn to_fields(&self) -> Vec<Field<A>> {
        match self {
            Self::Plaintext(plaintext) => plaintext.to_fields(),
            Self::Record(record) => record.to_fields(),
        }
    }
}
