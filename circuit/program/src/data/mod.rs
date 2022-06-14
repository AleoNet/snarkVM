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

// #[cfg(test)]
// use snarkvm_circuit_types::environment::assert_scope;

mod ciphertext;
pub use ciphertext::Ciphertext;

mod identifier;
pub use identifier::Identifier;

mod literal;
pub use literal::Literal;

mod plaintext;
pub use plaintext::Plaintext;

mod value;
pub use value::Value;

mod decrypt;
mod encrypt;
mod to_bits;
mod to_id;

use snarkvm_circuit_account::ViewKey;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Boolean, Field, Group, Scalar};

pub trait Visibility<A: Aleo>: ToBits<Boolean = Boolean<A>> + FromBits + ToFields + FromFields {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> u16;
}

pub struct Data<A: Aleo, Private: Visibility<A>>(Vec<(Identifier<A>, Value<A, Private>)>);

#[cfg(console)]
impl<A: Aleo> Inject for Data<A, Plaintext<A>> {
    type Primitive = console::Record<A::Network, console::Plaintext<A::Network>>;

    /// Initializes plaintext data from a primitive.
    fn new(mode: Mode, data: Self::Primitive) -> Self {
        // TODO (howardwu): Enforce the maximum number of data values.
        Self(Inject::new(mode, (*data).to_vec()))
    }
}

#[cfg(console)]
impl<A: Aleo> Inject for Data<A, Ciphertext<A>> {
    type Primitive = console::Record<A::Network, console::Ciphertext<A::Network>>;

    /// Initializes ciphertext data from a primitive.
    fn new(mode: Mode, data: Self::Primitive) -> Self {
        // TODO (howardwu): Enforce the maximum number of data values.
        Self(Inject::new(mode, (*data).to_vec()))
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Data<A, Plaintext<A>> {
    type Primitive = console::Record<A::Network, console::Plaintext<A::Network>>;

    /// Ejects the mode of the data.
    fn eject_mode(&self) -> Mode {
        self.0.iter().map(|(identifier, value)| (identifier, value).eject_mode()).collect::<Vec<_>>().eject_mode()
    }

    /// Ejects the data.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from(
            self.0.iter().map(|(identifier, value)| (identifier, value).eject_value()).collect::<Vec<_>>(),
        )
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Data<A, Ciphertext<A>> {
    type Primitive = console::Record<A::Network, console::Ciphertext<A::Network>>;

    /// Ejects the mode of the data.
    fn eject_mode(&self) -> Mode {
        self.0.iter().map(|(identifier, value)| (identifier, value).eject_mode()).collect::<Vec<_>>().eject_mode()
    }

    /// Ejects the data.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from(
            self.0.iter().map(|(identifier, value)| (identifier, value).eject_value()).collect::<Vec<_>>(),
        )
    }
}

#[cfg(console)]
impl<A: Aleo, Private: Visibility<A>> TypeName for Data<A, Private> {
    fn type_name() -> &'static str {
        "data"
    }
}
