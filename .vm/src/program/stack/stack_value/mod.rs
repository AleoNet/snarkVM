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

use console::{
    network::prelude::*,
    program::{Plaintext, Record},
    types::Field,
};

#[derive(Clone, PartialEq, Eq)]
pub enum StackValue<N: Network> {
    /// A plaintext value.
    Plaintext(Plaintext<N>),
    /// A record value.
    Record(Record<N, Plaintext<N>>),
}

impl<N: Network> ToBits for StackValue<N> {
    /// Returns the stack value as a list of **little-endian** bits.
    #[inline]
    fn to_bits_le(&self) -> Vec<bool> {
        match self {
            StackValue::Plaintext(plaintext) => plaintext.to_bits_le(),
            StackValue::Record(record) => record.to_bits_le(),
        }
    }

    /// Returns the stack value as a list of **big-endian** bits.
    #[inline]
    fn to_bits_be(&self) -> Vec<bool> {
        match self {
            StackValue::Plaintext(plaintext) => plaintext.to_bits_be(),
            StackValue::Record(record) => record.to_bits_be(),
        }
    }
}

impl<N: Network> ToFields for StackValue<N> {
    type Field = Field<N>;

    /// Returns the stack value as a list of fields.
    #[inline]
    fn to_fields(&self) -> Result<Vec<Self::Field>> {
        match self {
            StackValue::Plaintext(plaintext) => plaintext.to_fields(),
            StackValue::Record(record) => record.to_fields(),
        }
    }
}
