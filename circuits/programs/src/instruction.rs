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

use crate::{Immediate, Operand, Register};
use snarkvm_circuits::Environment;

pub enum Instruction<E: Environment> {
    /// Stores `operand` into `register`, if `register` is not already set.
    Store(Register<E>, Operand<E>),
    /// Adds `first` with `second`, storing the outcome in `register`.
    Add(Register<E>, Operand<E>, Operand<E>),
    /// Subtracts `first` from `second`, storing the outcome in `register`.
    Sub(Register<E>, Operand<E>, Operand<E>),
}

impl<E: Environment> Instruction<E> {
    /// Returns the opcode of the instruction.
    pub fn opcode(&self) -> u16 {
        match self {
            Self::Store(..) => 0,
            Self::Add(..) => 1,
            Self::Sub(..) => 2,
        }
    }

    /// Evaluates the instruction.
    pub fn evaluate(&self) {
        match self {
            Self::Store(register, operand) => Self::store(register, operand),
            Self::Add(register, first, second) => Self::add(register, first, second),
            Self::Sub(register, first, second) => Self::sub(register, first, second),
        }
    }

    /// Stores `operand` into `register`, if `register` is not already set.
    fn store(register: &Register<E>, operand: &Operand<E>) {
        register.store(operand.to_value())
    }

    /// Adds `first` with `second`, storing the outcome in `register`.
    fn add(register: &Register<E>, first: &Operand<E>, second: &Operand<E>) {
        match (first.to_value(), second.to_value()) {
            (Immediate::BaseField(a), Immediate::BaseField(b)) => register.store(Immediate::BaseField(a + b)),
            // (Immediate::Group(a), Immediate::Group(b)) => register.store(Immediate::Group(a + b)),
            _ => E::halt("Invalid 'add' instruction"),
        }
    }

    /// Subtracts `first` from `second`, storing the outcome in `register`.
    fn sub(register: &Register<E>, first: &Operand<E>, second: &Operand<E>) {
        match (first.to_value(), second.to_value()) {
            (Immediate::BaseField(a), Immediate::BaseField(b)) => register.store(Immediate::BaseField(a - b)),
            // (Immediate::Group(a), Immediate::Group(b)) => register.store(Immediate::Group(a - b)),
            _ => E::halt("Invalid 'sub' instruction"),
        }
    }
}
