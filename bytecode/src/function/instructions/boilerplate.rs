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

macro_rules! impl_instruction_boilerplate {
    ($instruction:ident, $op_type:ident, $op_code:expr) => {
        use crate::{
            function::{parsers::*, Instruction, Opcode},
            helpers::Register,
            Program,
            Value,
        };
        use snarkvm_circuits::{Parser, ParserResult};
        use snarkvm_utilities::{FromBytes, ToBytes};

        use core::fmt;
        use nom::combinator::map;
        use std::io::{Read, Result as IoResult, Write};

        impl<P: Program> $instruction<P> {
            /// Returns the operands of the instruction.
            pub fn operands(&self) -> Vec<Operand<P>> {
                self.operation.operands()
            }

            /// Returns the destination register of the instruction.
            pub fn destination(&self) -> &Register<P> {
                self.operation.destination()
            }
        }

        impl<P: Program> Opcode for $instruction<P> {
            /// Returns the opcode as a string.
            #[inline]
            fn opcode() -> &'static str {
                $op_code
            }
        }

        impl<P: Program> Parser for $instruction<P> {
            type Environment = P::Environment;

            #[inline]
            fn parse(string: &str) -> ParserResult<Self> {
                map($op_type::parse, |operation| Self { operation })(string)
            }
        }

        impl<P: Program> fmt::Display for $instruction<P> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.operation)
            }
        }

        impl<P: Program> FromBytes for $instruction<P> {
            fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
                Ok(Self { operation: $op_type::read_le(&mut reader)? })
            }
        }

        impl<P: Program> ToBytes for $instruction<P> {
            fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
                self.operation.write_le(&mut writer)
            }
        }

        #[allow(clippy::from_over_into)]
        impl<P: Program> Into<Instruction<P>> for $instruction<P> {
            /// Converts the operation into an instruction.
            fn into(self) -> Instruction<P> {
                Instruction::$instruction(self)
            }
        }
    };
}
