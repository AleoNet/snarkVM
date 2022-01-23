// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{traits::*, Affine, Environment};

use std::{fmt, ops::Deref};

#[derive(Clone)]
pub struct Address<E: Environment>(Affine<E>);

impl<E: Environment> Address<E> {
    ///
    /// Initializes a new instance of an address from an affine group.
    ///
    pub fn new(value: Affine<E>) -> Self {
        Self(value)
    }

    ///
    /// Returns `true` if the address is a constant.    
    ///
    pub fn is_constant(&self) -> bool {
        self.0.is_constant()
    }

    ///
    /// Ejects the address as a constant affine group element.
    ///
    pub fn eject_value(&self) -> E::Affine {
        self.0.eject_value()
    }
}

impl<E: Environment> fmt::Debug for Address<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

impl<E: Environment> Deref for Address<E> {
    type Target = Affine<E>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
