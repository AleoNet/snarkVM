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

use snarkvm_circuit_account::ComputeKey;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Boolean, Equal, Field, Group, Scalar};

pub struct SerialNumbers<A: Aleo> {
    /// The serial numbers.
    serial_numbers: Vec<Field<A>>,
    /// The signature for the serial numbers: `(challenge, response, compute_key, gammas)`.
    signature: (Scalar<A>, Scalar<A>, ComputeKey<A>, Vec<Group<A>>),
}

#[cfg(console)]
impl<A: Aleo> Inject for SerialNumbers<A> {
    type Primitive = console::SerialNumbers<A::Network>;

    /// Initializes the serial numbers from the given mode and native serial numbers.
    fn new(mode: Mode, serial_numbers: Self::Primitive) -> SerialNumbers<A> {
        Self {
            serial_numbers: Inject::new(mode, serial_numbers.value().to_vec()),
            signature: (
                Scalar::new(mode, serial_numbers.signature().0),
                Scalar::new(mode, serial_numbers.signature().1),
                ComputeKey::new(mode, serial_numbers.signature().2),
                Inject::new(mode, serial_numbers.signature().3.to_vec()),
            ),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for SerialNumbers<A> {
    type Primitive = console::SerialNumbers<A::Network>;

    /// Ejects the mode of the serial numbers.
    fn eject_mode(&self) -> Mode {
        (&self.serial_numbers, &self.signature.0, &self.signature.1, &self.signature.2, &self.signature.3).eject_mode()
    }

    /// Ejects the serial numbers.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from((self.serial_numbers.eject_value(), (&self.signature).eject_value()))
    }
}

impl<A: Aleo> SerialNumbers<A> {
    /// Returns the serial numbers.
    pub fn value(&self) -> &[Field<A>] {
        &self.serial_numbers
    }

    /// Returns the signature for the serial numbers.
    pub const fn signature(&self) -> &(Scalar<A>, Scalar<A>, ComputeKey<A>, Vec<Group<A>>) {
        &self.signature
    }
}
