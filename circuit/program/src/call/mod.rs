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

use crate::{CircuitValue, Identifier, ProgramID};
use snarkvm_circuit_account::Signature;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Boolean, Equal, Field, Group};

pub enum InputID<A: Aleo> {
    /// The hash of the constant input.
    Constant(Field<A>),
    /// The hash of the public input.
    Public(Field<A>),
    /// The index and commitment of the private input.
    Private(Field<A>, Field<A>),
    /// The `(commitment, H, r * H, gamma, serial_number)` tuple of the record input.
    Record(Field<A>, Group<A>, Group<A>, Group<A>, Field<A>),
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
            // Inject the expected index as `Mode::Private` and commitment as `Mode::Public`.
            console::InputID::Private(index, field) => {
                Self::Private(Field::new(Mode::Private, index), Field::new(Mode::Public, field))
            }
            // Inject the expected serial number as `Mode::Public`, and all other values as `Mode::Private`.
            console::InputID::Record(commitment, h, h_r, gamma, serial_number) => Self::Record(
                Field::new(Mode::Private, commitment),
                Group::new(Mode::Private, h),
                Group::new(Mode::Private, h_r),
                Group::new(Mode::Private, gamma),
                Field::new(Mode::Public, serial_number),
            ),
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
            Self::Private(index, field) => (index, field).eject_mode(),
            Self::Record(commitment, h, h_r, gamma, serial_number) => Mode::combine(commitment.eject_mode(), [
                h.eject_mode(),
                h_r.eject_mode(),
                gamma.eject_mode(),
                serial_number.eject_mode(),
            ]),
        }
    }

    /// Ejects the input ID as a primitive.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Self::Constant(field) => console::InputID::Constant(field.eject_value()),
            Self::Public(field) => console::InputID::Public(field.eject_value()),
            Self::Private(index, field) => console::InputID::Private(index.eject_value(), field.eject_value()),
            Self::Record(commitment, h, h_r, gamma, serial_number) => console::InputID::Record(
                commitment.eject_value(),
                h.eject_value(),
                h_r.eject_value(),
                gamma.eject_value(),
                serial_number.eject_value(),
            ),
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
            InputID::Private(index, field) => vec![index.clone(), field.clone()],
            InputID::Record(commitment, h, h_r, gamma, serial_number) => vec![
                commitment.clone(),
                h.to_x_coordinate(),
                h_r.to_x_coordinate(),
                gamma.to_x_coordinate(),
                serial_number.clone(),
            ],
        }
    }
}

pub struct Call<A: Aleo> {
    /// The request caller.
    caller: Address<A>,
    /// The program ID.
    program_id: ProgramID<A>,
    /// The function name.
    function_name: Identifier<A>,
    /// The function input IDs.
    input_ids: Vec<InputID<A>>,
    /// The function inputs.
    inputs: Vec<CircuitValue<A>>,
    /// The signature for the transition.
    signature: Signature<A>,
    /// The transition view key.
    tvk: Field<A>,
}

#[cfg(console)]
impl<A: Aleo> Inject for Call<A> {
    type Primitive = console::Call<A::Network>;

    /// Initializes the call from the given mode and console call.
    fn new(mode: Mode, call: Self::Primitive) -> Self {
        // Inject the inputs.
        let inputs = match call
            .input_ids()
            .iter()
            .zip_eq(call.inputs())
            .map(|(input_id, input)| {
                match input_id {
                    // A constant input is injected as `Mode::Constant`.
                    console::InputID::Constant(input_hash) => {
                        // Inject the input as `Mode::Constant`.
                        let input = CircuitValue::new(Mode::Constant, input.clone());
                        // Ensure the input is a plaintext.
                        ensure!(matches!(input, CircuitValue::Plaintext(..)), "Expected a plaintext input");
                        // Return the input.
                        Ok(input)
                    }
                    // A public input is injected as `Mode::Private`.
                    console::InputID::Public(input_hash) => {
                        // Inject the input as `Mode::Private`.
                        let input = CircuitValue::new(Mode::Private, input.clone());
                        // Ensure the input is a plaintext.
                        ensure!(matches!(input, CircuitValue::Plaintext(..)), "Expected a plaintext input");
                        // Return the input.
                        Ok(input)
                    }
                    // A private input is injected as `Mode::Private`.
                    console::InputID::Private(index, commitment) => {
                        // Inject the input as `Mode::Private`.
                        let input = CircuitValue::new(Mode::Private, input.clone());
                        // Ensure the input is a plaintext.
                        ensure!(matches!(input, CircuitValue::Plaintext(..)), "Expected a plaintext input");
                        // Return the input.
                        Ok(input)
                    }
                    // An input record is injected as `Mode::Private`.
                    console::InputID::Record(_, _, _, _, serial_number) => {
                        // Inject the input as `Mode::Private`.
                        let input = CircuitValue::new(Mode::Private, input.clone());
                        // Ensure the input is a record.
                        ensure!(matches!(input, CircuitValue::Record(..)), "Expected a record input");
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
            caller: Address::new(mode, *call.caller()),
            program_id: ProgramID::new(mode, *call.program_id()),
            function_name: Identifier::new(mode, *call.function_name()),
            input_ids: call.input_ids().iter().map(|input_id| InputID::new(mode, input_id.clone())).collect(),
            inputs,
            signature: Signature::new(mode, call.signature().clone()),
            tvk: Field::new(mode, *call.tvk()),
        }
    }
}

impl<A: Aleo> Call<A> {
    /// Returns the request caller.
    pub const fn caller(&self) -> &Address<A> {
        &self.caller
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
    pub fn inputs(&self) -> &[CircuitValue<A>] {
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
}

#[cfg(console)]
impl<A: Aleo> Eject for Call<A> {
    type Primitive = console::Call<A::Network>;

    /// Ejects the mode of the call.
    fn eject_mode(&self) -> Mode {
        Mode::combine(self.caller.eject_mode(), [
            self.program_id.eject_mode(),
            self.function_name.eject_mode(),
            self.input_ids.eject_mode(),
            self.inputs.eject_mode(),
            self.signature.eject_mode(),
            self.tvk.eject_mode(),
        ])
    }

    /// Ejects the call as a primitive.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from((
            self.caller.eject_value(),
            self.program_id.eject_value(),
            self.function_name.eject_value(),
            self.input_ids.iter().map(|input_id| input_id.eject_value()).collect(),
            self.inputs.eject_value(),
            self.signature.eject_value(),
            self.tvk.eject_value(),
        ))
    }
}
