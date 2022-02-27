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

use crate::Immediate;
use snarkvm_circuits::Environment;

use once_cell::unsync::OnceCell;
use std::{cell::RefCell, rc::Rc};

#[derive(Clone)]
pub struct Register<E: Environment>(u32, Rc<RefCell<OnceCell<Immediate<E>>>>);

impl<E: Environment> Register<E> {
    /// Returns a new instance of a register.
    pub(super) fn new(locator: u32) -> Register<E> {
        Self(locator, Default::default())
    }

    /// Returns `true` if the register at the given locator is already set.
    pub(super) fn is_set(&self) -> bool {
        self.1.borrow().get().is_some()
    }

    /// Attempts to store value into the register.
    pub(super) fn store(&self, value: Immediate<E>) {
        match self.1.borrow().get().is_some() {
            true => E::halt(format!("Register {} is already set", self.0)),
            false => if self.1.borrow().set(value).is_err() {
                E::halt(format!("Register {} failed to store value", self.0))
            }
        }
    }

    /// Attempts to load the value from the register.
    pub fn load(&self) -> Immediate<E> {
        match self.1.borrow().get() {
            Some(value) => value.clone(),
            None => E::halt(format!("Register {} is not set", self.0)),
        }
    }
}
