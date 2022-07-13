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
mod from_bits;
mod from_fields;
mod num_randomizers;
mod size_in_fields;
mod to_bits;
mod to_fields;

use crate::{Plaintext, Visibility};
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field};

use core::ops::Deref;

#[derive(Clone)]
pub struct Ciphertext<A: Aleo>(Vec<Field<A>>);

#[cfg(console)]
impl<A: Aleo> Inject for Ciphertext<A> {
    type Primitive = console::Ciphertext<A::Network>;

    /// Initializes a new ciphertext circuit from a primitive.
    fn new(mode: Mode, ciphertext: Self::Primitive) -> Self {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match (*ciphertext).len() <= A::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => Self(Inject::new(mode, (*ciphertext).to_vec())),
            false => A::halt("Ciphertext exceeds maximum allowed size"),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Ciphertext<A> {
    type Primitive = console::Ciphertext<A::Network>;

    /// Ejects the mode of the ciphertext.
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    /// Ejects the ciphertext.
    fn eject_value(&self) -> Self::Primitive {
        match console::FromFields::from_fields(&self.0.eject_value()) {
            Ok(ciphertext) => ciphertext,
            Err(error) => A::halt(format!("Failed to eject ciphertext: {error}")),
        }
    }
}

impl<A: Aleo> Deref for Ciphertext<A> {
    type Target = [Field<A>];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
