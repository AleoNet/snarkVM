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
mod num_randomizers;
mod to_bits;

use crate::{Ciphertext, Identifier, Plaintext, Visibility};
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean};

/// An entry stored in program data.
#[derive(Clone)]
pub enum Entry<A: Aleo, Private: Visibility<A>> {
    /// A constant entry.
    Constant(Plaintext<A>),
    /// A publicly-visible entry.
    Public(Plaintext<A>),
    /// A private entry encrypted under the address of the record owner.
    Private(Private),
}

#[cfg(console)]
impl<A: Aleo> Inject for Entry<A, Plaintext<A>> {
    type Primitive = console::Entry<A::Network, console::Plaintext<A::Network>>;

    /// Initializes a new plaintext entry from a primitive.
    fn new(mode: Mode, plaintext: Self::Primitive) -> Self {
        match plaintext {
            Self::Primitive::Constant(plaintext) => Self::Constant(Plaintext::new(mode, plaintext)),
            Self::Primitive::Public(plaintext) => Self::Public(Plaintext::new(mode, plaintext)),
            Self::Primitive::Private(plaintext) => Self::Private(Plaintext::new(mode, plaintext)),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Inject for Entry<A, Ciphertext<A>> {
    type Primitive = console::Entry<A::Network, console::Ciphertext<A::Network>>;

    /// Initializes a new ciphertext entry from a primitive.
    fn new(mode: Mode, plaintext: Self::Primitive) -> Self {
        match plaintext {
            Self::Primitive::Constant(plaintext) => Self::Constant(Plaintext::new(mode, plaintext)),
            Self::Primitive::Public(plaintext) => Self::Public(Plaintext::new(mode, plaintext)),
            Self::Primitive::Private(ciphertext) => Self::Private(Ciphertext::new(mode, ciphertext)),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Entry<A, Plaintext<A>> {
    type Primitive = console::Entry<A::Network, console::Plaintext<A::Network>>;

    /// Ejects the mode of the entry.
    fn eject_mode(&self) -> Mode {
        match self {
            Entry::Constant(_) => Mode::Constant,
            Entry::Public(_) => Mode::Public,
            Entry::Private(_) => Mode::Private,
        }
    }

    /// Ejects the entry.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Entry::Constant(plaintext) => Self::Primitive::Constant(plaintext.eject_value()),
            Entry::Public(plaintext) => Self::Primitive::Public(plaintext.eject_value()),
            Entry::Private(plaintext) => Self::Primitive::Private(plaintext.eject_value()),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Entry<A, Ciphertext<A>> {
    type Primitive = console::Entry<A::Network, console::Ciphertext<A::Network>>;

    /// Ejects the mode of the entry.
    fn eject_mode(&self) -> Mode {
        match self {
            Entry::Constant(_) => Mode::Constant,
            Entry::Public(_) => Mode::Public,
            Entry::Private(_) => Mode::Private,
        }
    }

    /// Ejects the entry.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Entry::Constant(plaintext) => Self::Primitive::Constant(plaintext.eject_value()),
            Entry::Public(plaintext) => Self::Primitive::Public(plaintext.eject_value()),
            Entry::Private(ciphertext) => Self::Primitive::Private(ciphertext.eject_value()),
        }
    }
}
