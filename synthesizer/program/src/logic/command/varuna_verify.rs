// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    traits::{RegistersLoad, RegistersLoadCircuit, RegistersStore, RegistersStoreCircuit, StackMatches, StackProgram},
    Opcode,
    Operand,
};
use circuit::prelude::ToFields as CircuitToFields;
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, PlaintextType, Register, RegisterType, ToFields as ConsoleToFields},
    types::Boolean,
};
use core::fmt;
use std::{
    fmt::{Debug, Display, Formatter},
    io::{Read, Write},
    str::FromStr,
};

/// Returns true if the Varuna `proof` is valid for the given `vk`s and `input`s and stores the result into `destination`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct VarunaVerify<N: Network> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network> VarunaVerify<N> {
    /// Initializes a new `varuna.verify` instruction.
    #[inline]
    pub fn new(operands: Vec<Operand<N>>, destination: Register<N>) -> Result<Self> {
        // Sanity check the number of operands.
        ensure!(operands.len() % 2 == 1, "Instruction '{}' must have an odd number of operands", Self::opcode());
        // Return the instruction.
        Ok(Self { operands, destination })
    }

    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Command("varuna.verify")
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that there is an odd number of operands.
        debug_assert!(self.operands.len() == 3, "Instruction '{}' must have an odd number of operands", Self::opcode());
        // Return the operands.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destination(&self) -> &Register<N> {
        &self.destination
    }
}

impl<N: Network> VarunaVerify<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() % 2 != 1 {
            bail!(
                "Instruction '{}' expects an odd number of operands, found {} operands",
                Self::opcode(),
                self.operands.len()
            )
        }

        // Retrieve the inputs.
        let data = match registers.load_literal(stack, &self.operands[0])? {
            Literal::Data(data) => data,
            _ => bail!("Expected the first operand to be a data object."),
        };

        // TODO: (@d0cd) Get VKs and verifiier inputs.
        todo!()
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoadCircuit<N, A> + RegistersStoreCircuit<N, A>),
    ) -> Result<()> {
        todo!()
    }

    /// Finalizes the instruction.
    #[inline]
    pub fn finalize(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        self.evaluate(stack, registers)
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(
        &self,
        _stack: &impl StackProgram<N>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        todo!()
    }
}

impl<N: Network> Parser for VarunaVerify<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        todo!()
    }
}

impl<N: Network> FromStr for VarunaVerify<N> {
    type Err = Error;

    /// Parses a string into an operation.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for VarunaVerify<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for VarunaVerify<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        todo!()
    }
}

impl<N: Network> FromBytes for VarunaVerify<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        todo!()
    }
}

impl<N: Network> ToBytes for VarunaVerify<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::MainnetV0;

    type CurrentNetwork = MainnetV0;

    #[test]
    fn test_parse() {
        let (string, varuna_verify) = VarunaVerify::<CurrentNetwork>::parse("varuna.verify r0 r1 r2 into r3").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(varuna_verify.operands.len(), 3, "The number of operands is incorrect");
        assert_eq!(
            varuna_verify.operands[0],
            Operand::Register(Register::Locator(0)),
            "The first operand is incorrect"
        );
        assert_eq!(
            varuna_verify.operands[1],
            Operand::Register(Register::Locator(1)),
            "The second operand is incorrect"
        );
        assert_eq!(
            varuna_verify.operands[2],
            Operand::Register(Register::Locator(2)),
            "The third operand is incorrect"
        );
        assert_eq!(varuna_verify.destination, Register::Locator(3), "The destination register is incorrect");
    }
}
