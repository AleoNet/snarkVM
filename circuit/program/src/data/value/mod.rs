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

mod decrypt;
mod encrypt;
mod num_randomizers;
mod to_bits;

use crate::{Ciphertext, Plaintext, Visibility};
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field};

/// A value stored in program data.
#[derive(Clone)]
pub enum Value<A: Aleo, Private: Visibility<A>> {
    /// A constant value.
    Constant(Plaintext<A>),
    /// A publicly-visible value.
    Public(Plaintext<A>),
    /// A private value encrypted under the account owner's address.
    Private(Private),
}

#[cfg(console)]
impl<A: Aleo> Inject for Value<A, Plaintext<A>> {
    type Primitive = console::Value<A::Network, console::Plaintext<A::Network>>;

    /// Initializes a new plaintext value from a primitive.
    fn new(mode: Mode, plaintext: Self::Primitive) -> Self {
        match plaintext {
            Self::Primitive::Constant(plaintext) => Self::Constant(Plaintext::new(mode, plaintext)),
            Self::Primitive::Public(plaintext) => Self::Public(Plaintext::new(mode, plaintext)),
            Self::Primitive::Private(plaintext) => Self::Private(Plaintext::new(mode, plaintext)),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Inject for Value<A, Ciphertext<A>> {
    type Primitive = console::Value<A::Network, console::Ciphertext<A::Network>>;

    /// Initializes a new ciphertext value from a primitive.
    fn new(mode: Mode, plaintext: Self::Primitive) -> Self {
        match plaintext {
            Self::Primitive::Constant(plaintext) => Self::Constant(Plaintext::new(mode, plaintext)),
            Self::Primitive::Public(plaintext) => Self::Public(Plaintext::new(mode, plaintext)),
            Self::Primitive::Private(ciphertext) => Self::Private(Ciphertext::new(mode, ciphertext)),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Value<A, Plaintext<A>> {
    type Primitive = console::Value<A::Network, console::Plaintext<A::Network>>;

    /// Ejects the mode of the value.
    fn eject_mode(&self) -> Mode {
        match self {
            Value::Constant(_) => Mode::Constant,
            Value::Public(_) => Mode::Public,
            Value::Private(_) => Mode::Private,
        }
    }

    /// Ejects the value.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Value::Constant(plaintext) => Self::Primitive::Constant(plaintext.eject_value()),
            Value::Public(plaintext) => Self::Primitive::Public(plaintext.eject_value()),
            Value::Private(plaintext) => Self::Primitive::Private(plaintext.eject_value()),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Value<A, Ciphertext<A>> {
    type Primitive = console::Value<A::Network, console::Ciphertext<A::Network>>;

    /// Ejects the mode of the value.
    fn eject_mode(&self) -> Mode {
        match self {
            Value::Constant(_) => Mode::Constant,
            Value::Public(_) => Mode::Public,
            Value::Private(_) => Mode::Private,
        }
    }

    /// Ejects the value.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Value::Constant(plaintext) => Self::Primitive::Constant(plaintext.eject_value()),
            Value::Public(plaintext) => Self::Primitive::Public(plaintext.eject_value()),
            Value::Private(ciphertext) => Self::Primitive::Private(ciphertext.eject_value()),
        }
    }
}

// impl<A: Aleo, Literal: EntryMode<A>> Entry<A, Literal> {
//     // /// Returns the recursive depth of this value.
//     // /// Note: Once `generic_const_exprs` is stabilized, this can be replaced with `const DEPTH: u8`.
//     // fn depth(&self, counter: usize) -> usize {
//     //     match self {
//     //         Self::Literal(..) => 1,
//     //         Self::Composite(composite) => {
//     //             // Determine the maximum depth of the composite.
//     //             let max_depth = composite.iter().map(|(_, value)| value.depth(counter)).fold(0, |a, b| a.max(b));
//     //             // Add `1` to the depth of the member with the largest depth.
//     //             max_depth.saturating_add(1)
//     //         }
//     //     }
//     // }
// }
