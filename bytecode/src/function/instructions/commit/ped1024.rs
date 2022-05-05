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

/// Performs a Pedersen commitment taking a 1024-bit value as input.
pub struct CommitPed1024<P: Program> {
    operation: BinaryOperation<P>,
}

impl<P: Program> CommitPed1024<P> {
    /// Returns the operands of the instruction.
    pub fn operands(&self) -> Vec<Operand<P>> {
        self.operation.operands()
    }

    /// Returns the destination register of the instruction.
    pub fn destination(&self) -> &Register<P> {
        self.operation.destination()
    }
}

impl<P: Program> Opcode for CommitPed1024<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "commit.ped1024"
    }
}

impl<P: Program> Parser for CommitPed1024<P> {
    type Environment = P::Environment;

    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        map(BinaryOperation::parse, |operation| Self { operation })(string)
    }
}

impl<P: Program> fmt::Display for CommitPed1024<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.operation)
    }
}

impl<P: Program> FromBytes for CommitPed1024<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { operation: BinaryOperation::read_le(&mut reader)? })
    }
}

impl<P: Program> ToBytes for CommitPed1024<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for CommitPed1024<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::CommitPed1024(self)
    }
}

impl<P: Program> Operation<P> for CommitPed1024<P> {
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
        let (_, instruction) = Instruction::<P>::parse("commit.ped1024 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitPed1024(_)));
    }

    test_modes!(
        address,
        CommitPed1024,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar",
        "889102317888271826718559972138868820466563749149942194168269228701119910350group"
    );
    test_modes!(
        bool,
        CommitPed1024,
        "true",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        field,
        CommitPed1024,
        "1field",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        group,
        CommitPed1024,
        "2group",
        "1scalar",
        "2664340318215809634698318956510253812463234504768303019123996597123255397816group"
    );
    test_modes!(
        i8,
        CommitPed1024,
        "1i8",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i16,
        CommitPed1024,
        "1i16",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i32,
        CommitPed1024,
        "1i32",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i64,
        CommitPed1024,
        "1i64",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i128,
        CommitPed1024,
        "1i128",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u8,
        CommitPed1024,
        "1u8",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u16,
        CommitPed1024,
        "1u16",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u32,
        CommitPed1024,
        "1u32",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u64,
        CommitPed1024,
        "1u64",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u128,
        CommitPed1024,
        "1u128",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        string,
        CommitPed1024,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar",
        "6258277521376623366396744618094324140083583859539902194155615459223370474204group"
    );
    test_modes!(
        scalar,
        CommitPed1024,
        "1scalar",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );

    test_instruction_halts!(
        string_halts,
        CommitPed1024,
        "The Pedersen hash input cannot exceed 1024 bits.",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
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

        CommitPed1024::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "7143232585354596727088537818886269936493413322580429357859918031397884359807group.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 1024 bits.")]
    fn test_composite_halts() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
            Literal::from_str("3field.private"),
            Literal::from_str("4field.private"),
            Literal::from_str("5field.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitPed1024::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
