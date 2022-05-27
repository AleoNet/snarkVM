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

mod bits;
mod bytes;
mod serialize;
mod string;

use snarkvm_console_network::Network;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBits,
    FromBytes,
    FromBytesDeserializer,
    ToBits,
    ToBytes,
    ToBytesSerializer,
};

use anyhow::{bail, Error, Result};
use core::{fmt, marker::PhantomData, str::FromStr};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

/// An identifier is an **immutable** UTF-8 string,
/// represented as a **constant** field element in the CurrentNetwork.
///
/// # Requirements
/// The identifier must not be an empty string.
/// The identifier must not start with a number.
/// The identifier must be alphanumeric, and may include underscores.
/// The identifier must not consist solely of underscores.
/// The identifier must fit within the data capacity of a base field element.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Identifier<N: Network>(String, PhantomData<N>);

impl<N: Network> TryFrom<&str> for Identifier<N> {
    type Error = Error;

    /// Initializes an identifier from a string.
    fn try_from(identifier: &str) -> Result<Self> {
        Self::from_str(identifier)
    }
}
