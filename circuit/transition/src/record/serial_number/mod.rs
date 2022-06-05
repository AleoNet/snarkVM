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

pub struct SerialNumber<A: Aleo> {
    /// The serial number.
    serial_number: Field<A>,
    /// The signature for the serial number: `(challenge, response, compute_key, gamma)`.
    signature: (Scalar<A>, Scalar<A>, ComputeKey<A>, Group<A>),
}

#[cfg(console)]
impl<A: Aleo> Inject for SerialNumber<A> {
    type Primitive = console::SerialNumber<A::Network>;

    /// Initializes a serial number from the given mode and native serial number.
    fn new(mode: Mode, serial_number: Self::Primitive) -> SerialNumber<A> {
        Self {
            serial_number: Field::new(mode, *serial_number.value()),
            signature: (
                Scalar::new(mode, serial_number.signature().0),
                Scalar::new(mode, serial_number.signature().1),
                ComputeKey::new(mode, serial_number.signature().2),
                Group::new(mode, serial_number.signature().3),
            ),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for SerialNumber<A> {
    type Primitive = console::SerialNumber<A::Network>;

    /// Ejects the mode of the serial number.
    fn eject_mode(&self) -> Mode {
        (&self.serial_number, &self.signature.0, &self.signature.1, &self.signature.2, &self.signature.3).eject_mode()
    }

    /// Ejects the serial number.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from((self.serial_number.eject_value(), (&self.signature).eject_value()))
    }
}

impl<A: Aleo> SerialNumber<A> {
    /// Returns the serial number.
    pub const fn value(&self) -> &Field<A> {
        &self.serial_number
    }

    /// Returns the signature for the serial number.
    pub const fn signature(&self) -> &(Scalar<A>, Scalar<A>, ComputeKey<A>, Group<A>) {
        &self.signature
    }
}
