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

mod find;
mod to_bits;
mod to_fields;

use crate::{Entry, Identifier, Plaintext, Record};
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field};

#[derive(Clone)]
pub enum Value<A: Aleo> {
    /// A plaintext value.
    Plaintext(Plaintext<A>),
    /// A record value.
    Record(Record<A, Plaintext<A>>),
}

impl<A: Aleo> Inject for Value<A> {
    type Primitive = console::Value<A::Network>;

    /// Initializes a circuit of the given mode and value.
    fn new(mode: Mode, value: Self::Primitive) -> Self {
        match value {
            console::Value::Plaintext(plaintext) => Value::Plaintext(Plaintext::new(mode, plaintext)),
            console::Value::Record(record) => Value::Record(Record::new(Mode::Private, record)),
        }
    }
}

impl<A: Aleo> Eject for Value<A> {
    type Primitive = console::Value<A::Network>;

    /// Ejects the mode of the circuit value.
    fn eject_mode(&self) -> Mode {
        match self {
            Value::Plaintext(plaintext) => plaintext.eject_mode(),
            Value::Record(record) => record.eject_mode(),
        }
    }

    /// Ejects the circuit value.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Value::Plaintext(plaintext) => console::Value::Plaintext(plaintext.eject_value()),
            Value::Record(record) => console::Value::Record(record.eject_value()),
        }
    }
}
