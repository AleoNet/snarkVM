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
mod string;

use console::{
    network::prelude::*,
    program::{Ciphertext, Plaintext},
    types::Field,
};

type Variant = u16;

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
    /// Returns the variant of the input.
    pub fn variant(&self) -> Variant {
        match self {
            Input::Constant(_, _) => 0,
            Input::Public(_, _) => 1,
            Input::Private(_, _) => 2,
            Input::Record(_) => 3,
            Input::ExternalRecord(_) => 4,
        }
    }

    /// Returns the ID of the input.
    pub fn id(&self) -> &Field<N> {
        match self {
            Input::Constant(id, _) => id,
            Input::Public(id, _) => id,
            Input::Private(id, _) => id,
            Input::Record(serial_number) => serial_number,
            Input::ExternalRecord(id) => id,
        }
    }

    /// Returns the serial number, if the input is a record.
    pub fn serial_number(&self) -> Option<&Field<N>> {
        match self {
            Input::Record(serial_number) => Some(serial_number),
            _ => None,
        }
    }

    /// Returns the public verifier inputs for the proof.
    pub fn verifier_inputs(&self) -> impl '_ + Iterator<Item = N::Field> {
        [self.id()].into_iter().map(|id| **id)
    }

    /// Returns `true` if the input is well-formed.
    /// If the optional value exists, this method checks that it hashes to the input ID.
    pub fn verify(&self) -> bool {
        // Ensure the hash of the value (if the value exists) is correct.
        let result = match self {
            Input::Constant(hash, Some(value)) => match N::hash_bhp1024(&value.to_bits_le()) {
                Ok(candidate_hash) => Ok(hash == &candidate_hash),
                Err(error) => Err(error),
            },
            Input::Public(hash, Some(value)) => match N::hash_bhp1024(&value.to_bits_le()) {
                Ok(candidate_hash) => Ok(hash == &candidate_hash),
                Err(error) => Err(error),
            },
            Input::Private(hash, Some(value)) => match N::hash_bhp1024(&value.to_bits_le()) {
                Ok(candidate_hash) => Ok(hash == &candidate_hash),
                Err(error) => Err(error),
            },
            _ => Ok(true),
        };

        match result {
            Ok(is_hash_valid) => is_hash_valid,
            Err(error) => {
                eprintln!("{error}");
                false
            }
        }
    }
}
