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
    program::{Ciphertext, Plaintext, Record},
    types::Field,
};

/// The transition output.
#[derive(Clone, PartialEq, Eq)]
pub enum Output<N: Network> {
    /// The plaintext hash and (optional) plaintext.
    Constant(Field<N>, Option<Plaintext<N>>),
    /// The plaintext hash and (optional) plaintext.
    Public(Field<N>, Option<Plaintext<N>>),
    /// The ciphertext hash and (optional) ciphertext.
    Private(Field<N>, Option<Ciphertext<N>>),
    /// The commitment, nonce, checksum, and (optional) record ciphertext.
    Record(Field<N>, Field<N>, Field<N>, Option<Record<N, Ciphertext<N>>>),
    /// The output commitment of the external record. Note: This is **not** the record commitment.
    ExternalRecord(Field<N>),
}

impl<N: Network> Output<N> {
    /// Returns the ID(s) of the output.
    pub fn id(&self) -> Vec<Field<N>> {
        match self {
            Output::Constant(id, ..) => vec![*id],
            Output::Public(id, ..) => vec![*id],
            Output::Private(id, ..) => vec![*id],
            Output::Record(commitment, nonce, checksum, _) => vec![*commitment, *nonce, *checksum],
            Output::ExternalRecord(id) => vec![*id],
        }
    }

    /// Returns the commitment if the output is a record.
    pub fn commitment(&self) -> Option<&Field<N>> {
        match self {
            Output::Record(commitment, ..) => Some(commitment),
            _ => None,
        }
    }

    /// Returns `true` if the output is well-formed.
    /// If the optional value exists, this method checks that it hashes to the input ID.
    pub fn verify(&self) -> bool {
        match self {
            Output::Constant(hash, Some(value)) => match N::hash_bhp1024(&value.to_bits_le()) {
                Ok(candidate_hash) => hash == &candidate_hash,
                Err(error) => {
                    eprintln!("{error}");
                    false
                }
            },
            Output::Public(hash, Some(value)) => match N::hash_bhp1024(&value.to_bits_le()) {
                Ok(candidate_hash) => hash == &candidate_hash,
                Err(error) => {
                    eprintln!("{error}");
                    false
                }
            },
            Output::Private(hash, Some(value)) => match N::hash_bhp1024(&value.to_bits_le()) {
                Ok(candidate_hash) => hash == &candidate_hash,
                Err(error) => {
                    eprintln!("{error}");
                    false
                }
            },
            Output::Record(_, _, checksum, Some(value)) => match N::hash_bhp1024(&value.to_bits_le()) {
                Ok(candidate_hash) => checksum == &candidate_hash,
                Err(error) => {
                    eprintln!("{error}");
                    false
                }
            },
            _ => true,
        }
    }
}

impl<N: Network> FromStr for Output<N> {
    type Err = Error;

    /// Initializes the output from a JSON-string.
    fn from_str(output: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(output)?)
    }
}

impl<N: Network> Debug for Output<N> {
    /// Prints the output as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Output<N> {
    /// Displays the output as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(ser::Error::custom)?)
    }
}
