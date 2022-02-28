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

use crate::{Immediate, Memory, Register};

#[derive(Clone)]
pub enum Operand<M: Memory> {
    Immediate(Immediate<M::Environment>),
    Register(Register),
}

impl<M: Memory> Operand<M> {
    /// Returns `true` if the value type is a register.
    pub(super) fn is_register(&self) -> bool {
        matches!(self, Self::Register(..))
    }

    /// Returns the value from a register, otherwise passes the loaded value through.
    pub(super) fn to_value(&self) -> Immediate<M::Environment> {
        match self {
            Self::Immediate(value) => value.clone(),
            Self::Register(register) => M::load(register),
        }
    }
}

impl<M: Memory> From<Immediate<M::Environment>> for Operand<M> {
    fn from(immediate: Immediate<M::Environment>) -> Operand<M> {
        Operand::Immediate(immediate)
    }
}

impl<M: Memory> From<&Immediate<M::Environment>> for Operand<M> {
    fn from(immediate: &Immediate<M::Environment>) -> Operand<M> {
        Operand::from(immediate.clone())
    }
}

impl<M: Memory> From<Register> for Operand<M> {
    fn from(register: Register) -> Operand<M> {
        Operand::Register(register)
    }
}

impl<M: Memory> From<&Register> for Operand<M> {
    fn from(register: &Register) -> Operand<M> {
        Operand::from(register.clone())
    }
}
