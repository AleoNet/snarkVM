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

use super::Commit;
use crate::{
    function::{parsers::*, Instruction, Opcode, Operation, Registers},
    Program,
    Value,
};
use snarkvm_circuits::{algorithms::Pedersen512, CommitmentScheme, Parser, ParserResult};
use snarkvm_utilities::{FromBytes, ToBytes};

use nom::combinator::map;
use snarkvm_circuits::{Literal, ToBits};
use std::io::{Read, Result as IoResult, Write};

/// Performs a Pedersen commitment taking a 512-bit value as input.
pub type CommitPed512<P> = Commit<P, Pedersen512<<P as Program>::Aleo>>;

impl<P: Program> Opcode for CommitPed512<P> {
    /// Returns the opcode as a string.
    #[inline]
    fn opcode() -> &'static str {
        "commit.ped512"
    }
}

impl<P: Program> Parser for CommitPed512<P> {
    type Environment = P::Environment;

    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        map(BinaryOperation::parse, |operation| Self {
            operation,
            commitment_gadget: Pedersen512::<P::Environment>::setup("PedersenCircuit0"),
        })(string)
    }
}

impl<P: Program> FromBytes for CommitPed512<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self {
            operation: BinaryOperation::read_le(&mut reader)?,
            commitment_gadget: Pedersen512::<P::Environment>::setup("PedersenCircuit0"),
        })
    }
}

impl<P: Program> ToBytes for CommitPed512<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.operation.write_le(&mut writer)
    }
}

#[allow(clippy::from_over_into)]
impl<P: Program> Into<Instruction<P>> for CommitPed512<P> {
    /// Converts the operation into an instruction.
    fn into(self) -> Instruction<P> {
        Instruction::CommitPed512(self)
    }
}

impl<P: Program> Operation<P> for CommitPed512<P> {
    /// Evaluates the operation.
    #[inline]
    fn evaluate(&self, registers: &Registers<P>) {
        impl_commit_evaluate!(self, registers);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_instruction_halts, test_modes, Identifier, Process, Register};

    type P = Process;

    #[test]
    fn test_parse() {
        let (_, instruction) = Instruction::<P>::parse("commit.ped512 r0 r1 into r2;").unwrap();
        assert!(matches!(instruction, Instruction::CommitPed512(_)));
    }

    test_modes!(
        address,
        CommitPed512,
        "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah",
        "1scalar",
        "889102317888271826718559972138868820466563749149942194168269228701119910350group"
    );
    test_modes!(
        bool,
        CommitPed512,
        "true",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        field,
        CommitPed512,
        "1field",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        group,
        CommitPed512,
        "2group",
        "1scalar",
        "2664340318215809634698318956510253812463234504768303019123996597123255397816group"
    );
    test_modes!(
        i8,
        CommitPed512,
        "1i8",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i16,
        CommitPed512,
        "1i16",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i32,
        CommitPed512,
        "1i32",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i64,
        CommitPed512,
        "1i64",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        i128,
        CommitPed512,
        "1i128",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u8,
        CommitPed512,
        "1u8",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u16,
        CommitPed512,
        "1u16",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u32,
        CommitPed512,
        "1u32",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u64,
        CommitPed512,
        "1u64",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        u128,
        CommitPed512,
        "1u128",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );
    test_modes!(
        string,
        CommitPed512,
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
        "1scalar",
        "4594816090259059137299110253863905613404195254146009928650302617756911006842group"
    );
    test_modes!(
        scalar,
        CommitPed512,
        "1scalar",
        "1scalar",
        "7143232585354596727088537818886269936493413322580429357859918031397884359807group"
    );

    test_instruction_halts!(
        string_halts,
        CommitPed512,
        "The Pedersen hash input cannot exceed 512 bits.",
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"",
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

        CommitPed512::from_str("r0 r1 into r2").evaluate(&registers);

        let value = registers.load(&Register::from_str("r2"));
        let expected = Value::<P>::from_str(
            "7143232585354596727088537818886269936493413322580429357859918031397884359807group.private",
        );
        assert_eq!(expected, value);
    }

    #[test]
    #[should_panic(expected = "The Pedersen hash input cannot exceed 512 bits.")]
    fn test_composite_halts() {
        let first = Value::<P>::Composite(Identifier::from_str("message"), vec![
            Literal::from_str("1field.public"),
            Literal::from_str("2field.private"),
            Literal::from_str("3field.private"),
        ]);
        let second = Value::<P>::from_str("1scalar");

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), first);
        registers.assign(&Register::from_str("r1"), second);

        CommitPed512::from_str("r0 r1 into r2").evaluate(&registers);
    }
}
