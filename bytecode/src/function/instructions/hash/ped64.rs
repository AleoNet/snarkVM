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

use crate::{
    function::{parsers::*, Instruction, Opcode, Operation, Registers},
    helpers::Register,
    Program,
    Value,
};
use snarkvm_circuits::{Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use core::fmt;
use nom::combinator::map;
use snarkvm_circuits::{Aleo, Literal, ToBits};
use std::io::{Read, Result as IoResult, Write};

/// Performs a Pedersen hash taking a 64-bit value as input.
pub struct HashPed64<P: Program> {
    operation: UnaryOperation<P>,
}

impl<P: Program> HashPed64<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for HashPed64<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "hash.ped64"
    }
}

impl<P: Program> Parser for HashPed64<P> {
    type Environment = P::Environment;

    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        map(UnaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for HashPed64<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for HashPed64<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: UnaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for HashPed64<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for HashPed64<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::HashPed64(self)
    }
}

impl<P: Program> Operation<P> for HashPed64<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        impl_pedersen_evaluate!(self, registers);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("hash.ped64 r0 into r1;").unwrap();
        assert!(matches!(instruction, Instruction::HashPed64(_)));
    }

    test_modes!(
        bool,
        HashPed64,
        "true",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i8,
        HashPed64,
        "1i8",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i16,
        HashPed64,
        "1i16",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i32,
        HashPed64,
        "1i32",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        i64,
        HashPed64,
        "1i64",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u8,
        HashPed64,
        "1u8",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u16,
        HashPed64,
        "1u16",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u32,
        HashPed64,
        "1u32",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        u64,
        HashPed64,
        "1u64",
        "6122249396247477588925765696834100286827340493907798245233656838221917119242field"
    );
    test_modes!(
        string,
        HashPed64,
        "\"aaaaaaaa\"",
        "7299801179261936372670032123063256554706653150313868761081445373623581679329field"
    );

    test_instruction_halts!(
        address_halts,
        HashPed64,
        "The Pedersen hash input cannot exceed 64 bits.",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah"
    );
    test_instruction_halts!(field_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "1field");
    test_instruction_halts!(group_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "2group");
    test_instruction_halts!(scalar_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "1scalar");
    test_instruction_halts!(i128_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "1i128");
    test_instruction_halts!(u128_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "1u128");
    test_instruction_halts!(string_halts, HashPed64, "The Pedersen hash input cannot exceed 64 bits.", "\"aaaaaaaaa\"");

    #[test]
    fn test_composite() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("true.public"),
            Literal::from_str("false.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed64::from_str("r0 into r1").evaluate(&registers);

        let value = registers.load(&Register::from_str("r1"));
        let expected = Value::<P>::from_str(
            "6122249396247477588925765696834100286827340493907798245233656838221917119242field.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 64 bits.")]
    fn test_composite_halts() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("false.private"),
        ]);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), first);

        HashPed64::from_str("r0 into r1").evaluate(&registers);
    }
}
