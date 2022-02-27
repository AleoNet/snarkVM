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

use crate::{Immediate, Register};
use snarkvm_circuits::Environment;

#[derive(Clone)]
pub enum Operand<E: Environment> {
    Immediate(Immediate<E>),
    Register(Register<E>),
}

impl<E: Environment> Operand<E> {
    /// Returns `true` if the value type is a register.
    pub(super) fn is_register(&self) -> bool {
        matches!(self, Self::Register(..))
    }

    /// Returns the value from a register, otherwise passes the loaded value through.
    pub(super) fn to_value(&self) -> Immediate<E> {
        match self {
            Self::Immediate(value) => value.clone(),
            Self::Register(register) => register.load(),
        }
    }
}

impl<E: Environment> From<Immediate<E>> for Operand<E> {
    fn from(immediate: Immediate<E>) -> Operand<E> {
        Operand::Immediate(immediate)
    }
}

impl<E: Environment> From<&Immediate<E>> for Operand<E> {
    fn from(immediate: &Immediate<E>) -> Operand<E> {
        Operand::from(immediate.clone())
    }
}

impl<E: Environment> From<Register<E>> for Operand<E> {
    fn from(register: Register<E>) -> Operand<E> {
        Operand::Register(register)
    }
}

impl<E: Environment> From<&Register<E>> for Operand<E> {
    fn from(register: &Register<E>) -> Operand<E> {
        Operand::from(register.clone())
    }
}
