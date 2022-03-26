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
use snarkvm_circuits_types::environment::assert_scope;

use snarkvm_circuits_types::{environment::prelude::*, Scalar};

/// The account view key is able to decrypt records and ciphertext messages.
pub struct ViewKey<E: Environment>(Scalar<E>);

impl<E: Environment> Inject for ViewKey<E> {
    type Primitive = E::ScalarField;

    /// Initializes an account view key from the given mode and scalar field element.
    fn new(mode: Mode, value: Self::Primitive) -> ViewKey<E> {
        Self(Scalar::new(mode, value))
    }
}

impl<E: Environment> Eject for ViewKey<E> {
    type Primitive = E::ScalarField;

    ///
    /// Ejects the mode of the view key.
    ///
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    ///
    /// Ejects the view key as a scalar field element.
    ///
    fn eject_value(&self) -> Self::Primitive {
        self.0.eject_value()
    }
}
