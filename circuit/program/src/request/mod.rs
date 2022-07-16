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

mod to_tpk;
mod verify;

use crate::{Identifier, ProgramID, Value};
use snarkvm_circuit_account::Signature;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Boolean, Equal, Field, Group, Scalar, U16};

pub enum InputID<A: Aleo> {
    /// The hash of the constant input.
    Constant(Field<A>),
    /// The hash of the public input.
    Public(Field<A>),
    /// The ciphertext hash of the private input.
    Private(Field<A>),
    /// The `(gamma, serial_number)` tuple of the record input.
    Record(Group<A>, Field<A>),
    /// The commitment of the external record input.
    ExternalRecord(Field<A>),
}

#[cfg(console)]
impl<A: Aleo> Inject for InputID<A> {
    type Primitive = console::InputID<A::Network>;

    /// Initializes the input ID from the given mode and console input ID.
    fn new(_: Mode, input: Self::Primitive) -> Self {
        match input {
            // Inject the expected hash as `Mode::Constant`.
            console::InputID::Constant(field) => Self::Constant(Field::new(Mode::Constant, field)),
            // Inject the expected hash as `Mode::Public`.
            console::InputID::Public(field) => Self::Public(Field::new(Mode::Public, field)),
            // Inject the ciphertext hash as `Mode::Public`.
            console::InputID::Private(field) => Self::Private(Field::new(Mode::Public, field)),
            // Inject gamma as `Mode::Private` and the expected serial number as `Mode::Public`.
            console::InputID::Record(gamma, serial_number) => {
                Self::Record(Group::new(Mode::Private, gamma), Field::new(Mode::Public, serial_number))
            }
            // Inject the commitment as `Mode::Public`.
            console::InputID::ExternalRecord(field) => Self::ExternalRecord(Field::new(Mode::Public, field)),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for InputID<A> {
    type Primitive = console::InputID<A::Network>;

    /// Ejects the mode of the input ID.
    fn eject_mode(&self) -> Mode {
        match self {
            Self::Constant(field) => field.eject_mode(),
            Self::Public(field) => field.eject_mode(),
            Self::Private(field) => field.eject_mode(),
            Self::Record(gamma, serial_number) => Mode::combine(gamma.eject_mode(), [serial_number.eject_mode()]),
            Self::ExternalRecord(field) => field.eject_mode(),
        }
    }

    /// Ejects the input ID as a primitive.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Self::Constant(field) => console::InputID::Constant(field.eject_value()),
            Self::Public(field) => console::InputID::Public(field.eject_value()),
            Self::Private(field) => console::InputID::Private(field.eject_value()),
            Self::Record(gamma, serial_number) => {
                console::InputID::Record(gamma.eject_value(), serial_number.eject_value())
            }
            Self::ExternalRecord(field) => console::InputID::ExternalRecord(field.eject_value()),
        }
    }
}

impl<A: Aleo> ToFields for InputID<A> {
    type Field = Field<A>;

    /// Returns the input as a list of field elements.
    fn to_fields(&self) -> Vec<Self::Field> {
        match self {
            InputID::Constant(field) => vec![field.clone()],
            InputID::Public(field) => vec![field.clone()],
            InputID::Private(field) => vec![field.clone()],
            InputID::Record(gamma, serial_number) => vec![gamma.to_x_coordinate(), serial_number.clone()],
            InputID::ExternalRecord(field) => vec![field.clone()],
        }
    }
}

pub struct Request<A: Aleo> {
    /// The request caller.
    caller: Address<A>,
    /// The network ID.
    network_id: U16<A>,
    /// The program ID.
    program_id: ProgramID<A>,
    /// The function name.
    function_name: Identifier<A>,
    /// The function input IDs.
    input_ids: Vec<InputID<A>>,
    /// The function inputs.
    inputs: Vec<Value<A>>,
    /// The signature for the transition.
    signature: Signature<A>,
    /// The transition view key.
    tvk: Field<A>,
    /// The transition secret key.
    tsk: Scalar<A>,
}

#[cfg(console)]
impl<A: Aleo> Inject for Request<A> {
    type Primitive = console::Request<A::Network>;

    /// Initializes the request from the given mode and console request.
    fn new(mode: Mode, request: Self::Primitive) -> Self {
        // Inject the inputs.
        let inputs = match request
            .input_ids()
            .iter()
            .zip_eq(request.inputs())
            .map(|(input_id, input)| {
                match input_id {
                    // A constant input is injected as `Mode::Constant`.
                    console::InputID::Constant(..) => {
                        // Inject the input as `Mode::Constant`.
                        let input = Value::new(Mode::Constant, input.clone());
                        // Ensure the input is a plaintext.
                        ensure!(matches!(input, Value::Plaintext(..)), "Expected a plaintext input");
                        // Return the input.
                        Ok(input)
                    }
                    // A public input is injected as `Mode::Private`.
                    console::InputID::Public(..) => {
                        // Inject the input as `Mode::Private`.
                        let input = Value::new(Mode::Private, input.clone());
                        // Ensure the input is a plaintext.
                        ensure!(matches!(input, Value::Plaintext(..)), "Expected a plaintext input");
                        // Return the input.
                        Ok(input)
                    }
                    // A private input is injected as `Mode::Private`.
                    console::InputID::Private(..) => {
                        // Inject the input as `Mode::Private`.
                        let input = Value::new(Mode::Private, input.clone());
                        // Ensure the input is a plaintext.
                        ensure!(matches!(input, Value::Plaintext(..)), "Expected a plaintext input");
                        // Return the input.
                        Ok(input)
                    }
                    // A record input is injected as `Mode::Private`.
                    console::InputID::Record(..) => {
                        // Inject the input as `Mode::Private`.
                        let input = Value::new(Mode::Private, input.clone());
                        // Ensure the input is a record.
                        ensure!(matches!(input, Value::Record(..)), "Expected a record input");
                        // Return the input.
                        Ok(input)
                    }
                    // An external record input is injected as `Mode::Private`.
                    console::InputID::ExternalRecord(..) => {
                        // Inject the input as `Mode::Private`.
                        let input = Value::new(Mode::Private, input.clone());
                        // Ensure the input is a record.
                        ensure!(matches!(input, Value::Record(..)), "Expected an external record input");
                        // Return the input.
                        Ok(input)
                    }
                }
            })
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(inputs) => inputs,
            Err(error) => A::halt(format!("{error}")),
        };

        Self {
            caller: Address::new(mode, *request.caller()),
            network_id: U16::new(Mode::Constant, *request.network_id()),
            program_id: ProgramID::new(Mode::Constant, *request.program_id()),
            function_name: Identifier::new(Mode::Constant, *request.function_name()),
            input_ids: request.input_ids().iter().map(|input_id| InputID::new(Mode::Public, *input_id)).collect(),
            inputs,
            signature: Signature::new(mode, *request.signature()),
            tvk: Field::new(mode, *request.tvk()),
            tsk: Scalar::new(mode, *request.tsk()),
        }
    }
}

impl<A: Aleo> Request<A> {
    /// Returns the request caller.
    pub const fn caller(&self) -> &Address<A> {
        &self.caller
    }

    /// Returns the network ID.
    pub const fn network_id(&self) -> &U16<A> {
        &self.network_id
    }

    /// Returns the program ID.
    pub const fn program_id(&self) -> &ProgramID<A> {
        &self.program_id
    }

    /// Returns the function name.
    pub const fn function_name(&self) -> &Identifier<A> {
        &self.function_name
    }

    /// Returns the input IDs for the transition.
    pub fn input_ids(&self) -> &[InputID<A>] {
        &self.input_ids
    }

    /// Returns the function inputs.
    pub fn inputs(&self) -> &[Value<A>] {
        &self.inputs
    }

    /// Returns the signature for the transition.
    pub const fn signature(&self) -> &Signature<A> {
        &self.signature
    }

    /// Returns the transition view key.
    pub const fn tvk(&self) -> &Field<A> {
        &self.tvk
    }

    /// Returns the transition secret key.
    pub const fn tsk(&self) -> &Scalar<A> {
        &self.tsk
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Request<A> {
    type Primitive = console::Request<A::Network>;

    /// Ejects the mode of the request.
    fn eject_mode(&self) -> Mode {
        Mode::combine(self.caller.eject_mode(), [
            self.network_id.eject_mode(),
            self.program_id.eject_mode(),
            self.function_name.eject_mode(),
            self.input_ids.eject_mode(),
            self.inputs.eject_mode(),
            self.signature.eject_mode(),
            self.tvk.eject_mode(),
            self.tsk.eject_mode(),
        ])
    }

    /// Ejects the request as a primitive.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from((
            self.caller.eject_value(),
            self.network_id.eject_value(),
            self.program_id.eject_value(),
            self.function_name.eject_value(),
            self.input_ids.iter().map(|input_id| input_id.eject_value()).collect(),
            self.inputs.eject_value(),
            self.signature.eject_value(),
            self.tvk.eject_value(),
            self.tsk.eject_value(),
        ))
    }
}
