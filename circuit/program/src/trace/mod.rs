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

use crate::{Identifier, ProgramID, Request};
use snarkvm_circuit_account::Signature;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Boolean, Equal, Field, Group, Scalar};

pub enum InputID<A: Aleo> {
    /// The hash of the constant input.
    Constant(Field<A>),
    /// The hash of the public input.
    Public(Field<A>),
    /// The commitment of the private input.
    Private(Field<A>),
    /// The `(commitment, H, r * H, gamma, serial_number)` tuple of the record input.
    Record(Field<A>, Group<A>, Group<A>, Group<A>, Field<A>),
}

#[cfg(console)]
impl<A: Aleo> Inject for InputID<A> {
    type Primitive = console::InputID<A::Network>;

    /// Initializes the input ID from the given mode and console input ID.
    fn new(mode: Mode, input: Self::Primitive) -> Self {
        match input {
            console::InputID::Constant(field) => Self::Constant(Field::new(mode, field)),
            console::InputID::Public(field) => Self::Public(Field::new(mode, field)),
            console::InputID::Private(field) => Self::Private(Field::new(mode, field)),
            console::InputID::Record(commitment, h, h_r, gamma, serial_number) => Self::Record(
                Field::new(mode, commitment),
                Group::new(mode, h),
                Group::new(mode, h_r),
                Group::new(mode, gamma),
                Field::new(mode, serial_number),
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
            Self::Private(field) => field.eject_mode(),
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
            Self::Private(field) => console::InputID::Private(field.eject_value()),
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
            InputID::Private(field) => vec![field.clone()],
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

pub struct Trace<A: Aleo> {
    /// The request caller.
    caller: Address<A>,
    /// The program ID.
    program_id: ProgramID<A>,
    /// The function name.
    function_name: Identifier<A>,
    /// The function input IDs.
    input_ids: Vec<InputID<A>>,
    /// The signature for the transition.
    signature: Signature<A>,
    /// The transition view key.
    tvk: Field<A>,
}

#[cfg(console)]
impl<A: Aleo> Inject for Trace<A> {
    type Primitive = console::Trace<A::Network>;

    /// Initializes the trace from the given mode and console trace.
    fn new(mode: Mode, trace: Self::Primitive) -> Self {
        Self {
            caller: Address::new(mode, *trace.caller()),
            program_id: ProgramID::new(mode, *trace.program_id()),
            function_name: Identifier::new(mode, *trace.function_name()),
            input_ids: trace.input_ids().iter().map(|input_id| InputID::new(mode, input_id.clone())).collect(),
            signature: Signature::new(mode, trace.signature().clone()),
            tvk: Field::new(mode, *trace.tvk()),
        }
    }
}

impl<A: Aleo> Trace<A> {
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
impl<A: Aleo> Eject for Trace<A> {
    type Primitive = console::Trace<A::Network>;

    /// Ejects the mode of the trace.
    fn eject_mode(&self) -> Mode {
        Mode::combine(self.caller.eject_mode(), [
            self.program_id.eject_mode(),
            self.function_name.eject_mode(),
            self.input_ids.eject_mode(),
            self.signature.eject_mode(),
            self.tvk.eject_mode(),
        ])
    }

    /// Ejects the trace as a primitive.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from((
            self.caller.eject_value(),
            self.program_id.eject_value(),
            self.function_name.eject_value(),
            self.input_ids.iter().map(|input_id| input_id.eject_value()).collect(),
            self.signature.eject_value(),
            self.tvk.eject_value(),
        ))
    }
}
