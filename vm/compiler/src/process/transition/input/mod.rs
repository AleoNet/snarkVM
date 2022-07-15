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
mod serialize;

use console::{
    network::prelude::*,
    program::{Ciphertext, Plaintext},
    types::Field,
};

/// The transition input.
#[derive(Clone, PartialEq, Eq)]
pub enum Input<N: Network> {
    /// The plaintext hash and (optional) plaintext.
    Constant(Field<N>, Option<Plaintext<N>>),
    /// The plaintext hash and (optional) plaintext.
    Public(Field<N>, Option<Plaintext<N>>),
    /// The ciphertext hash and (optional) ciphertext.
    Private(Field<N>, Option<Ciphertext<N>>),
    /// The serial number.
    Record(Field<N>),
    /// The input commitment to the external record. Note: This is **not** the record commitment.
    ExternalRecord(Field<N>),
}

impl<N: Network> Input<N> {
    /// Returns the ID of the input.
    pub fn id(&self) -> Field<N> {
        match self {
            Input::Constant(id, _) => *id,
            Input::Public(id, _) => *id,
            Input::Private(id, _) => *id,
            Input::Record(id) => *id,
            Input::ExternalRecord(id) => *id,
        }
    }

    /// Returns the serial number, if the input is a record.
    pub fn serial_number(&self) -> Option<&Field<N>> {
        match self {
            Input::Record(serial_number) => Some(serial_number),
            _ => None,
        }
    }

    /// Returns `true` if the input is well-formed.
    /// If the optional value exists, this method checks that it hashes to the input ID.
    pub fn verify(&self) -> bool {
        match self {
            Input::Constant(hash, Some(value)) => match N::hash_bhp1024(&value.to_bits_le()) {
                Ok(candidate_hash) => hash == &candidate_hash,
                Err(error) => {
                    eprintln!("{error}");
                    false
                }
            },
            Input::Public(hash, Some(value)) => match N::hash_bhp1024(&value.to_bits_le()) {
                Ok(candidate_hash) => hash == &candidate_hash,
                Err(error) => {
                    eprintln!("{error}");
                    false
                }
            },
            Input::Private(hash, Some(value)) => match N::hash_bhp1024(&value.to_bits_le()) {
                Ok(candidate_hash) => hash == &candidate_hash,
                Err(error) => {
                    eprintln!("{error}");
                    false
                }
            },
            _ => true,
        }
    }
}

impl<N: Network> FromStr for Input<N> {
    type Err = Error;

    /// Initializes the input from a JSON-string.
    fn from_str(input: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(input)?)
    }
}

impl<N: Network> Debug for Input<N> {
    /// Prints the input as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Input<N> {
    /// Displays the input as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(ser::Error::custom)?)
    }
}
