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

use crate::StackValue;

#[derive(Clone)]
pub enum CircuitValue<A: circuit::Aleo> {
    /// A plaintext value.
    Plaintext(circuit::Plaintext<A>),
    /// A record value.
    Record(circuit::program::Record<A, circuit::Plaintext<A>>),
}

impl<A: circuit::Aleo> CircuitValue<A> {
    /// Returns the circuit value as a list of **little-endian** bits.
    #[inline]
    pub fn to_bits_le(&self) -> Vec<circuit::types::Boolean<A>> {
        use circuit::ToBits;

        match self {
            CircuitValue::Plaintext(plaintext) => plaintext.to_bits_le(),
            CircuitValue::Record(record) => record.to_bits_le(),
        }
    }
}

impl<A: circuit::Aleo> circuit::Inject for CircuitValue<A> {
    type Primitive = StackValue<A::Network>;

    /// Initializes a circuit of the given mode and value.
    fn new(mode: circuit::Mode, value: Self::Primitive) -> Self {
        match value {
            StackValue::Plaintext(plaintext) => CircuitValue::Plaintext(circuit::Plaintext::new(mode, plaintext)),
            StackValue::Record(record) => CircuitValue::Record(circuit::program::Record::new(mode, record)),
        }
    }
}

impl<A: circuit::Aleo> circuit::Eject for CircuitValue<A> {
    type Primitive = StackValue<A::Network>;

    /// Ejects the mode of the circuit value.
    fn eject_mode(&self) -> circuit::Mode {
        match self {
            CircuitValue::Plaintext(plaintext) => plaintext.eject_mode(),
            CircuitValue::Record(record) => record.eject_mode(),
        }
    }

    /// Ejects the circuit value.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            CircuitValue::Plaintext(plaintext) => StackValue::Plaintext(plaintext.eject_value()),
            CircuitValue::Record(record) => StackValue::Record(record.eject_value()),
        }
    }
}
