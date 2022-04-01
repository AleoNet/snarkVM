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
    /// The opcode of the instruction.
    opcode: &'static str,
    /// The operands of the instruction.
    operands: Vec<Operand<E>>,
    /// The destination register.
    destination: Register<E>,
}

impl<E: Environment> Instruction<E> {
    /// Initializes a new instruction.
    ///
    /// # Errors
    /// This method will halt if any operand values are not constant.
    /// This method will halt if the destination register is a register member.
    /// This method will halt if any operand registers are greater than *or equal to* the destination register.
    #[inline]
    pub fn new(opcode: &'static str, operands: Vec<Operand<E>>, destination: Register<E>) -> Self {
        // Ensure the operand values are constant.
        for value in operands.iter().filter_map(|operand| operand.value()) {
            if !value.is_constant() {
                E::halt(format!("Operand {value} must be a constant value"))
            }
        }

        // Ensure the destination register is not a register member.
        if let Register::Member(..) = destination {
            E::halt("Destination register cannot be a register member")
        }

        // Ensure the operands do not contain registers greater than or equal to the destination register.
        for register in operands.iter().filter_map(|operand| operand.register()) {
            if register.locator() >= destination.locator() {
                E::halt(format!("Operand register {register} is greater than the destination {destination}"))
            }
        }

        Self { opcode, operands, destination }
    }

    /// Returns the instruction opcode, such as `add`.
    #[inline]
    pub fn opcode(&self) -> &'static str {
        self.opcode
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
            self.opcode,
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
        self.opcode == other.opcode
            && self.operands.len() == other.operands.len()
            && self.destination == other.destination
    }
}

impl<E: Environment> Eq for Instruction<E> {}
