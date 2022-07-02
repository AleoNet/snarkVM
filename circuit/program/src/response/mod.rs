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

mod verify;

use crate::CircuitValue;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Equal, Field};

pub enum OutputID<A: Aleo> {
    /// The hash of the constant output.
    Constant(Field<A>),
    /// The hash of the public output.
    Public(Field<A>),
    /// The index and ciphertext hash of the private output.
    Private(Field<A>, Field<A>),
    /// The `(index, commitment, nonce, checksum)` tuple of the record output.
    Record(Field<A>, Field<A>, Field<A>, Field<A>),
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
            // Inject the expected index as `Mode::Private` and ciphertext hash as `Mode::Public`.
            console::OutputID::Private(index, field) => {
                Self::Private(Field::new(Mode::Constant, index), Field::new(Mode::Public, field))
            }
            // Inject the expected commitment, nonce, and checksum as `Mode::Public`.
            console::OutputID::Record(index, commitment, nonce, checksum) => Self::Record(
                Field::new(Mode::Constant, index),
                Field::new(Mode::Public, commitment),
                Field::new(Mode::Public, nonce),
                Field::new(Mode::Public, checksum),
            ),
        }
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
            Self::Private(index, field) => (index, field).eject_mode(),
            Self::Record(index, commitment, nonce, checksum) => {
                Mode::combine(index.eject_mode(), [commitment.eject_mode(), nonce.eject_mode(), checksum.eject_mode()])
            }
        }
    }

    /// Ejects the output ID as a primitive.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Self::Constant(field) => console::OutputID::Constant(field.eject_value()),
            Self::Public(field) => console::OutputID::Public(field.eject_value()),
            Self::Private(index, field) => console::OutputID::Private(index.eject_value(), field.eject_value()),
            Self::Record(index, commitment, nonce, checksum) => console::OutputID::Record(
                index.eject_value(),
                commitment.eject_value(),
                nonce.eject_value(),
                checksum.eject_value(),
            ),
        }
    }
}

pub struct Response<A: Aleo> {
    /// The function output IDs.
    output_ids: Vec<OutputID<A>>,
    /// The function outputs.
    outputs: Vec<CircuitValue<A>>,
}

#[cfg(console)]
impl<A: Aleo> Inject for Response<A> {
    type Primitive = console::Response<A::Network>;

    /// Initializes the response from the given mode and console response.
    fn new(_: Mode, response: Self::Primitive) -> Self {
        // Inject the outputs.
        let outputs = match response
            .output_ids()
            .iter()
            .zip_eq(response.outputs())
            .map(|(output_id, output)| {
                match output_id {
                    // A constant output is injected as `Mode::Constant`.
                    console::OutputID::Constant(..) => {
                        // Inject the output as `Mode::Constant`.
                        let output = CircuitValue::new(Mode::Constant, output.clone());
                        // Ensure the output is a plaintext.
                        ensure!(matches!(output, CircuitValue::Plaintext(..)), "Expected a plaintext output");
                        // Return the output.
                        Ok(output)
                    }
                    // A public output is injected as `Mode::Private`.
                    console::OutputID::Public(..) => {
                        // Inject the output as `Mode::Private`.
                        let output = CircuitValue::new(Mode::Private, output.clone());
                        // Ensure the output is a plaintext.
                        ensure!(matches!(output, CircuitValue::Plaintext(..)), "Expected a plaintext output");
                        // Return the output.
                        Ok(output)
                    }
                    // A private output is injected as `Mode::Private`.
                    console::OutputID::Private(..) => {
                        // Inject the output as `Mode::Private`.
                        let output = CircuitValue::new(Mode::Private, output.clone());
                        // Ensure the output is a plaintext.
                        ensure!(matches!(output, CircuitValue::Plaintext(..)), "Expected a plaintext output");
                        // Return the output.
                        Ok(output)
                    }
                    // An output record is injected as `Mode::Private`.
                    console::OutputID::Record(..) => {
                        // Inject the output as `Mode::Private`.
                        let output = CircuitValue::new(Mode::Private, output.clone());
                        // Ensure the output is a record.
                        ensure!(matches!(output, CircuitValue::Record(..)), "Expected a record output");
                        // Return the output.
                        Ok(output)
                    }
                }
            })
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(outputs) => outputs,
            Err(error) => A::halt(format!("{error}")),
        };

        Self {
            output_ids: response
                .output_ids()
                .iter()
                .map(|output_id| OutputID::new(Mode::Public, output_id.clone()))
                .collect(),
            outputs,
        }
    }
}

impl<A: Aleo> Response<A> {
    /// Returns the output IDs for the transition.
    pub fn output_ids(&self) -> &[OutputID<A>] {
        &self.output_ids
    }

    /// Returns the function outputs.
    pub fn outputs(&self) -> &[CircuitValue<A>] {
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
