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

mod to_bits;
mod to_fields;

use crate::Identifier;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field};

/// A program ID is of the form `{name}.{network}`.
/// If no `network`-level domain is specified, the default network is used.
#[derive(Clone)]
pub struct ProgramID<A: Aleo> {
    /// The program name.
    name: Identifier<A>,
    /// The network-level domain (NLD).
    network: Identifier<A>,
}

#[cfg(console)]
impl<A: Aleo> Inject for ProgramID<A> {
    type Primitive = console::ProgramID<A::Network>;

    /// Injects a program ID with the given primitive.
    fn new(_: Mode, id: Self::Primitive) -> Self {
        Self {
            name: Identifier::new(Mode::Constant, *id.name()),
            network: Identifier::new(Mode::Constant, *id.network()),
        }
    }
}

impl<A: Aleo> ProgramID<A> {
    /// Returns the program name.
    #[inline]
    pub const fn name(&self) -> &Identifier<A> {
        &self.name
    }

    /// Returns the network-level domain (NLD).
    #[inline]
    pub const fn network(&self) -> &Identifier<A> {
        &self.network
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for ProgramID<A> {
    type Primitive = console::ProgramID<A::Network>;

    /// Ejects the mode of the program ID.
    fn eject_mode(&self) -> Mode {
        Mode::Constant
    }

    /// Ejects a program ID into a primitive.
    fn eject_value(&self) -> Self::Primitive {
        console::ProgramID::from((self.name.eject_value(), self.network.eject_value()))
    }
}
