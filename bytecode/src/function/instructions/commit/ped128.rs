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

/// Performs a Pedersen commitment taking a 128-bit value as input.
pub struct CommitPed128<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> CommitPed128<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for CommitPed128<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "commit.ped128"
    }
}

impl<P: Program> Parser for CommitPed128<P> {
    type Environment = P::Environment;

    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        map(BinaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for CommitPed128<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for CommitPed128<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for CommitPed128<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for CommitPed128<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::CommitPed128(self)
    }
}

impl<P: Program> Operation<P> for CommitPed128<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        impl_commit_evaluate!(self, registers);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.ped128 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitPed128(_)));
    }

    test_modes!(
        bool,
        CommitPed128,
        "true",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i8,
        CommitPed128,
        "1i8",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i16,
        CommitPed128,
        "1i16",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i32,
        CommitPed128,
        "1i32",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i64,
        CommitPed128,
        "1i64",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i128,
        CommitPed128,
        "1i128",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u8,
        CommitPed128,
        "1u8",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u16,
        CommitPed128,
        "1u16",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u32,
        CommitPed128,
        "1u32",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u64,
        CommitPed128,
        "1u64",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u128,
        CommitPed128,
        "1u128",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        string,
        CommitPed128,
        "\"aaaaaaaaaaaaaaaa\"",
        "1scalar",
        "379417118045898520789123124736668719236348888564273665391158449346246489573group"
    );

    test_instruction_halts!(
        address_halts,
        CommitPed128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar"
    );
    test_instruction_halts!(
        field_halts,
        CommitPed128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "1field",
        "1scalar"
    );
    test_instruction_halts!(
        group_halts,
        CommitPed128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "2group",
        "1scalar"
    );
    test_instruction_halts!(
        scalar_halts,
        CommitPed128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "1scalar",
        "1scalar"
    );
    test_instruction_halts!(
        string_halts,
        CommitPed128,
        "The Pedersen hash input cannot exceed 128 bits.",
        "\"aaaaaaaaaaaaaaaaaa\"",
        "1scalar"
    );

    #[test]
    fn test_composite() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("true.public"),
            Literal::from_str("false.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitPed128::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "7143232585354596727088537818886269936493413322580429357859918031397884359807group.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 128 bits.")]
    fn test_composite_halts() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("false.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitPed128::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
