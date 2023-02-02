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

mod bytes;
mod equal;
mod find;
mod parse;
mod serialize;
mod to_bits;
mod to_fields;

use crate::{Entry, Identifier, Plaintext, Record};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

#[derive(Clone)]
pub enum Value<N: Network> {
    /// A plaintext value.
    Plaintext(Plaintext<N>),
    /// A record value.
    Record(Record<N, Plaintext<N>>),
}

impl<N: Network> From<&Value<N>> for Value<N> {
    /// Returns a clone of the value.
    fn from(value: &Value<N>) -> Self {
        value.clone()
    }
}

impl<N: Network> TryFrom<Result<Value<N>>> for Value<N> {
    type Error = Error;

    /// Initializes a value from a result.
    fn try_from(value: Result<Value<N>>) -> Result<Self> {
        value
    }
}

impl<N: Network> TryFrom<String> for Value<N> {
    type Error = Error;

    /// Initializes a value from a string.
    fn try_from(value: String) -> Result<Self> {
        Self::from_str(&value)
    }
}

impl<N: Network> TryFrom<&String> for Value<N> {
    type Error = Error;

    /// Initializes a value from a string.
    fn try_from(value: &String) -> Result<Self> {
        Self::from_str(value)
    }
}

impl<N: Network> TryFrom<&str> for Value<N> {
    type Error = Error;

    /// Initializes a value from a string.
    fn try_from(value: &str) -> Result<Self> {
        Self::from_str(value)
    }
}
