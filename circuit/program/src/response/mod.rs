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

#[cfg(test)]
use snarkvm_circuit_types::environment::assert_scope;

mod from_outputs;
mod process_outputs_from_callback;

use crate::{Identifier, ProgramID, Value};
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Field};

pub enum OutputID<A: Aleo> {
    /// The hash of the constant output.
    Constant(Field<A>),
    /// The hash of the public output.
    Public(Field<A>),
    /// The ciphertext hash of the private output.
    Private(Field<A>),
    /// The `(commitment, nonce, checksum)` tuple of the record output.
    Record(Field<A>, Field<A>, Field<A>),
    /// The commitment of the external record output.
    ExternalRecord(Field<A>),
}

#[cfg(console)]
impl<A: Aleo> Inject for OutputID<A> {
    type Primitive = console::OutputID<A::Network>;

    /// Initializes the output ID from the given mode and console output ID.
    fn new(_: Mode, output: Self::Primitive) -> Self {
        match output {
            // Inject the expected hash as `Mode::Constant`.
            console::OutputID::Constant(field) => Self::Constant(Field::new(Mode::Constant, field)),
            // Inject the expected hash as `Mode::Public`.
            console::OutputID::Public(field) => Self::Public(Field::new(Mode::Public, field)),
            // Inject the ciphertext hash as `Mode::Public`.
            console::OutputID::Private(field) => Self::Private(Field::new(Mode::Public, field)),
            // Inject the expected commitment, nonce, and checksum as `Mode::Public`.
            console::OutputID::Record(commitment, nonce, checksum) => Self::Record(
                Field::new(Mode::Public, commitment),
                Field::new(Mode::Public, nonce),
                Field::new(Mode::Public, checksum),
            ),
            // Inject the expected commitment as `Mode::Public`.
            console::OutputID::ExternalRecord(commitment) => Self::ExternalRecord(Field::new(Mode::Public, commitment)),
        }
    }
}

impl<A: Aleo> OutputID<A> {
    /// Initializes a constant output ID.
    fn constant(expected_hash: Field<A>) -> Self {
        // Inject the expected hash as `Mode::Constant`.
        let output_hash = Field::new(Mode::Constant, expected_hash.eject_value());
        // Ensure the injected hash matches the given hash.
        A::assert_eq(&output_hash, expected_hash);
        // Return the output ID.
        Self::Constant(output_hash)
    }

    /// Initializes a public output ID.
    fn public(expected_hash: Field<A>) -> Self {
        // Inject the expected hash as `Mode::Public`.
        let output_hash = Field::new(Mode::Public, expected_hash.eject_value());
        // Ensure the injected hash matches the given hash.
        A::assert_eq(&output_hash, expected_hash);
        // Return the output ID.
        Self::Public(output_hash)
    }

    /// Initializes a private output ID.
    fn private(expected_hash: Field<A>) -> Self {
        // Inject the ciphertext hash as `Mode::Public`.
        let output_hash = Field::new(Mode::Public, expected_hash.eject_value());
        // Ensure the injected hash matches the given hash.
        A::assert_eq(&output_hash, expected_hash);
        // Return the output ID.
        Self::Private(output_hash)
    }

    /// Initializes a record output ID.
    fn record(expected_commitment: Field<A>, expected_nonce: Field<A>, expected_checksum: Field<A>) -> Self {
        // Inject the expected commitment, nonce, and checksum as `Mode::Public`.
        let output_commitment = Field::new(Mode::Public, expected_commitment.eject_value());
        let output_nonce = Field::new(Mode::Public, expected_nonce.eject_value());
        let output_checksum = Field::new(Mode::Public, expected_checksum.eject_value());
        // Ensure the injected commitment, nonce, and checksum match the given commitment, nonce, and checksum.
        A::assert_eq(&output_commitment, expected_commitment);
        A::assert_eq(&output_nonce, expected_nonce);
        A::assert_eq(&output_checksum, expected_checksum);
        // Return the output ID.
        Self::Record(output_commitment, output_nonce, output_checksum)
    }

    /// Initializes an external record output ID.
    fn external_record(expected_commitment: Field<A>) -> Self {
        // Inject the expected commitment as `Mode::Public`.
        let output_commitment = Field::new(Mode::Public, expected_commitment.eject_value());
        // Ensure the injected commitment matches the given commitment.
        A::assert_eq(&output_commitment, expected_commitment);
        // Return the output ID.
        Self::ExternalRecord(output_commitment)
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for OutputID<A> {
    type Primitive = console::OutputID<A::Network>;

    /// Ejects the mode of the output ID.
    fn eject_mode(&self) -> Mode {
        match self {
            Self::Constant(field) => field.eject_mode(),
            Self::Public(field) => field.eject_mode(),
            Self::Private(field) => field.eject_mode(),
            Self::Record(commitment, nonce, checksum) => {
                Mode::combine(commitment.eject_mode(), [nonce.eject_mode(), checksum.eject_mode()])
            }
            Self::ExternalRecord(commitment) => commitment.eject_mode(),
        }
    }

    /// Ejects the output ID as a primitive.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Self::Constant(field) => console::OutputID::Constant(field.eject_value()),
            Self::Public(field) => console::OutputID::Public(field.eject_value()),
            Self::Private(field) => console::OutputID::Private(field.eject_value()),
            Self::Record(commitment, nonce, checksum) => {
                console::OutputID::Record(commitment.eject_value(), nonce.eject_value(), checksum.eject_value())
            }
            Self::ExternalRecord(commitment) => console::OutputID::ExternalRecord(commitment.eject_value()),
        }
    }
}

pub struct Response<A: Aleo> {
    /// The function output IDs.
    output_ids: Vec<OutputID<A>>,
    /// The function outputs.
    outputs: Vec<Value<A>>,
}

impl<A: Aleo> Response<A> {
    /// Returns the output IDs for the transition.
    pub fn output_ids(&self) -> &[OutputID<A>] {
        &self.output_ids
    }

    /// Returns the function outputs.
    pub fn outputs(&self) -> &[Value<A>] {
        &self.outputs
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Response<A> {
    type Primitive = console::Response<A::Network>;

    /// Ejects the mode of the response.
    fn eject_mode(&self) -> Mode {
        Mode::combine(self.output_ids.eject_mode(), [self.outputs.eject_mode()])
    }

    /// Ejects the response as a primitive.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from((
            self.output_ids.iter().map(|output_id| output_id.eject_value()).collect(),
            self.outputs.eject_value(),
        ))
    }
}
