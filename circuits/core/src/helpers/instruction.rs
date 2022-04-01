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

use crate::{Operand, Register};
use snarkvm_circuits_types::prelude::*;

use core::fmt;

// pub enum Opcode {
//     Simple(Primary),
//     Complex(Primary, Secondary)
// }

/// The instruction represents a single instruction in the program.
#[derive(Clone, Debug)]
pub struct Instruction<E: Environment> {
    /// The instruction name.
    name: &'static str,
    /// The operands of the instruction.
    operands: Vec<Operand<E>>,
    /// The destination register.
    destination: Register<E>,
}

impl<E: Environment> Instruction<E> {
    /// Initializes a new instruction.
    ///
    /// # Errors
    /// This function will halt if the given destination register is a register member.
    /// This function will halt if any given operand is a value and is non-constant.
    #[inline]
    pub fn new(name: &'static str, destination: Register<E>, operands: Vec<Operand<E>>) -> Self {
        // Ensure the destination register is not a register member.
        if let Register::Member(..) = destination {
            E::halt("Destination register cannot be a register member")
        }

        // Ensure if any operand is a value, that it is constant.
        for operand in operands.iter() {
            if let Operand::Value(value) = operand {
                if !value.is_constant() {
                    E::halt("Operand cannot be a non-constant value")
                }
            }
        }

        Self { name, destination, operands }
    }

    /// Returns the instruction name.
    /// This is the name of the instruction, such as `add`.
    #[inline]
    pub fn name(&self) -> &'static str {
        self.name
    }

    /// Returns the operands of the instruction.
    /// These are the registers and values that the instruction will read from.
    #[inline]
    pub fn operands(&self) -> &[Operand<E>] {
        &self.operands
    }

    /// Returns the destination register.
    /// This is the register that the instruction will write its result into.
    #[inline]
    pub fn destination(&self) -> &Register<E> {
        &self.destination
    }
}

impl<E: Environment> fmt::Display for Instruction<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} {} into {};",
            self.name,
            self.operands.iter().map(|operand| operand.to_string()).collect::<Vec<_>>().join(" "),
            self.destination,
        )
    }
}

impl<E: Environment> PartialEq for Instruction<E> {
    /// The destination register can only be assigned once.
    /// As such, an equivalence relation can be constructed based on this assumption,
    /// as an instruction may only ever write to a given destination register once.
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.operands.len() == other.operands.len() && self.destination == other.destination
    }
}

impl<E: Environment> Eq for Instruction<E> {}
