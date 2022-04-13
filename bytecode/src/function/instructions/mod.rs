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

pub(super) mod add;
pub(super) use add::*;

pub(super) mod and;
pub(super) use and::*;

pub(super) mod add_wrapped;
pub(super) use add_wrapped::*;

pub(super) mod div;
pub(super) use div::*;

pub(super) mod div_wrapped;
pub(super) use div_wrapped::*;

pub(super) mod equal;
pub(super) use equal::*;

pub(super) mod mul;
pub(super) use mul::*;

pub(super) mod mul_wrapped;
pub(super) use mul_wrapped::*;

pub(super) mod neg;
pub(super) use neg::*;

pub(super) mod not;
pub(super) use not::*;

pub(super) mod or;
pub(super) use or::*;

pub(super) mod sub;
pub(super) use sub::*;

pub(super) mod sub_wrapped;
pub(super) use sub_wrapped::*;

pub(super) mod xor;
pub(super) use xor::*;

use crate::{
    function::{parsers::Operand, registers::Registers},
    helpers::Register,
    Program,
    Sanitizer,
};
use snarkvm_circuits::{Parser, ParserResult};
use snarkvm_utilities::{error, FromBytes, ToBytes};

use core::fmt;
use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::map,
    sequence::{pair, preceded},
};
use std::io::{Read, Result as IoResult, Write};

/// Creates a match statement that produces the count for a binary instruction.
///
/// ## Example
/// ```ignore
/// match_count!(
///     match AddWrappedCircuit::count(case) {
///         (I8, I8) => I8,
///         (I16, I16) => I16,
///         (I32, I32) => I32,
///         (I64, I64) => I64,
///         (I128, I128) => I128,
///         (U8, U8) => U8,
///         (U16, U16) => U16,
///         (U32, U32) => U32,
///         (U64, U64) => U64,
///         (U128, U128) => U128,
///     }
/// )
/// ```
#[macro_export]
macro_rules! match_count {
    (match $operation:tt::$macro_:ident($case:expr) { $( ($input_a:ident, $input_b:ident) => $output:ident, )+ }) => {{
        match $case {
            $(
                (LiteralType::$input_a(mode_a), LiteralType::$input_b(mode_b)) => {
                    $macro_!($input_a<P::Environment>, $operation<$input_b<P::Environment>, Output = $output<P::Environment>>, &(*mode_a, *mode_b))
                }
            ),+
            _ => P::halt(format!("Invalid '{}' instruction", Self::opcode())),
        }
    }};
}

pub trait Opcode {
    ///
    /// Returns the opcode of the operation.
    ///
    fn opcode() -> &'static str;
}

pub trait Operation<P: Program>: Parser + Into<Instruction<P>> {
    ///
    /// Evaluates the operation.
    ///
    fn evaluate(&self, registers: &Registers<P>);
}

pub enum Instruction<P: Program> {
    /// Adds `first` with `second`, storing the outcome in `destination`.
    Add(Add<P>),
    /// Adds `first` with `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    AddWrapped(AddWrapped<P>),
    /// Performs a bitwise AND operation on `first` and `second`, storing the outcome in `destination`.
    And(And<P>),
    /// Divides `first` by `second`, storing the outcome in `destination`.
    Div(Div<P>),
    /// Divides `first` by `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    DivWrapped(DivWrapped<P>),
    /// Checks if `first` is equal to `second`, storing the outcome in `destination`.
    Equal(Equal<P>),
    /// Multiplies `first` with `second`, storing the outcome in `destination`.
    Mul(Mul<P>),
    /// Multiplies `first` with `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    MulWrapped(MulWrapped<P>),
    /// Negates `first`, storing the outcome in `destination`.
    Neg(Neg<P>),
    /// Flips each bit in the representation of `first`, storing the outcome in `destination`.
    Not(Not<P>),
    /// Performs a bitwise Or on `first` and `second`, storing the outcome in `destination`.
    Or(Or<P>),
    /// Subtracts `second` from `first`, storing the outcome in `destination`.
    Sub(Sub<P>),
    /// Subtracts `second` from `first`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    SubWrapped(SubWrapped<P>),
    /// Performs a bitwise Xor on `first` and `second`, storing the outcome in `destination`.
    Xor(Xor<P>),
}

impl<P: Program> Instruction<P> {
    /// Returns the opcode of the instruction.
    #[inline]
    pub(crate) fn opcode(&self) -> &'static str {
        match self {
            Self::Add(..) => Add::<P>::opcode(),
            Self::AddWrapped(..) => AddWrapped::<P>::opcode(),
            Self::And(..) => And::<P>::opcode(),
            Self::Div(..) => Div::<P>::opcode(),
            Self::DivWrapped(..) => DivWrapped::<P>::opcode(),
            Self::Equal(..) => Equal::<P>::opcode(),
            Self::Mul(..) => Mul::<P>::opcode(),
            Self::MulWrapped(..) => MulWrapped::<P>::opcode(),
            Self::Neg(..) => Neg::<P>::opcode(),
            Self::Not(..) => Not::<P>::opcode(),
            Self::Or(..) => Or::<P>::opcode(),
            Self::Sub(..) => Sub::<P>::opcode(),
            Self::SubWrapped(..) => SubWrapped::<P>::opcode(),
            Self::Xor(..) => Xor::<P>::opcode(),
        }
    }

    /// Returns the operands of the instruction.
    #[inline]
    pub(crate) fn operands(&self) -> Vec<Operand<P>> {
        match self {
            Self::Add(add) => add.operands(),
            Self::AddWrapped(add_wrapped) => add_wrapped.operands(),
            Self::And(and) => and.operands(),
            Self::Div(div) => div.operands(),
            Self::DivWrapped(div_wrapped) => div_wrapped.operands(),
            Self::Equal(equal) => equal.operands(),
            Self::Mul(mul) => mul.operands(),
            Self::MulWrapped(mul_wrapped) => mul_wrapped.operands(),
            Self::Neg(neg) => neg.operands(),
            Self::Not(not) => not.operands(),
            Self::Or(or) => or.operands(),
            Self::Sub(sub) => sub.operands(),
            Self::SubWrapped(sub_wrapped) => sub_wrapped.operands(),
            Self::Xor(xor) => xor.operands(),
        }
    }

    /// Returns the destination register of the instruction.
    #[inline]
    pub(crate) fn destination(&self) -> &Register<P> {
        match self {
            Self::Add(add) => add.destination(),
            Self::AddWrapped(add_wrapped) => add_wrapped.destination(),
            Self::And(and) => and.destination(),
            Self::Div(div) => div.destination(),
            Self::DivWrapped(div_wrapped) => div_wrapped.destination(),
            Self::Equal(equal) => equal.destination(),
            Self::Mul(mul) => mul.destination(),
            Self::MulWrapped(mul_wrapped) => mul_wrapped.destination(),
            Self::Neg(neg) => neg.destination(),
            Self::Not(not) => not.destination(),
            Self::Or(or) => or.destination(),
            Self::Sub(sub) => sub.destination(),
            Self::SubWrapped(sub_wrapped) => sub_wrapped.destination(),
            Self::Xor(xor) => xor.destination(),
        }
    }

    /// Evaluates the instruction.
    #[inline]
    pub(crate) fn evaluate(&self, registers: &Registers<P>) {
        match self {
            Self::Add(instruction) => instruction.evaluate(registers),
            Self::AddWrapped(instruction) => instruction.evaluate(registers),
            Self::And(instruction) => instruction.evaluate(registers),
            Self::Div(instruction) => instruction.evaluate(registers),
            Self::DivWrapped(instruction) => instruction.evaluate(registers),
            Self::Equal(instruction) => instruction.evaluate(registers),
            Self::Mul(instruction) => instruction.evaluate(registers),
            Self::MulWrapped(instruction) => instruction.evaluate(registers),
            Self::Neg(instruction) => instruction.evaluate(registers),
            Self::Not(instruction) => instruction.evaluate(registers),
            Self::Or(instruction) => instruction.evaluate(registers),
            Self::Sub(instruction) => instruction.evaluate(registers),
            Self::SubWrapped(instruction) => instruction.evaluate(registers),
            Self::Xor(instruction) => instruction.evaluate(registers),
        }
    }
}

impl<P: Program> Parser for Instruction<P> {
    type Environment = P::Environment;

    /// Parses a string into an instruction.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the instruction from the string.
        let (string, instruction) = alt((
            // Note that order of the individual parsers matters.
            preceded(pair(tag(Add::<P>::opcode()), tag(" ")), map(Add::parse, Into::into)),
            preceded(pair(tag(AddWrapped::<P>::opcode()), tag(" ")), map(AddWrapped::parse, Into::into)),
            preceded(pair(tag(And::<P>::opcode()), tag(" ")), map(And::parse, Into::into)),
            preceded(pair(tag(Div::<P>::opcode()), tag(" ")), map(Div::parse, Into::into)),
            preceded(pair(tag(DivWrapped::<P>::opcode()), tag(" ")), map(DivWrapped::parse, Into::into)),
            preceded(pair(tag(Equal::<P>::opcode()), tag(" ")), map(Equal::parse, Into::into)),
            preceded(pair(tag(Mul::<P>::opcode()), tag(" ")), map(Mul::parse, Into::into)),
            preceded(pair(tag(MulWrapped::<P>::opcode()), tag(" ")), map(MulWrapped::parse, Into::into)),
            preceded(pair(tag(Neg::<P>::opcode()), tag(" ")), map(Neg::parse, Into::into)),
            preceded(pair(tag(Not::<P>::opcode()), tag(" ")), map(Not::parse, Into::into)),
            preceded(pair(tag(Or::<P>::opcode()), tag(" ")), map(Or::parse, Into::into)),
            preceded(pair(tag(Sub::<P>::opcode()), tag(" ")), map(Sub::parse, Into::into)),
            preceded(pair(tag(SubWrapped::<P>::opcode()), tag(" ")), map(SubWrapped::parse, Into::into)),
            preceded(pair(tag(Xor::<P>::opcode()), tag(" ")), map(Xor::parse, Into::into)),
        ))(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, instruction))
    }
}

impl<P: Program> fmt::Display for Instruction<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Add(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::AddWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::And(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Div(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::DivWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Equal(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Mul(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::MulWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Neg(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Not(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Or(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Sub(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::SubWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Xor(instruction) => write!(f, "{} {};", self.opcode(), instruction),
        }
    }
}

impl<P: Program> FromBytes for Instruction<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let code = u16::read_le(&mut reader)?;
        match code {
            0 => Ok(Self::Add(Add::read_le(&mut reader)?)),
            1 => Ok(Self::AddWrapped(AddWrapped::read_le(&mut reader)?)),
            2 => Ok(Self::And(And::read_le(&mut reader)?)),
            3 => Ok(Self::Div(Div::read_le(&mut reader)?)),
            4 => Ok(Self::DivWrapped(DivWrapped::read_le(&mut reader)?)),
            5 => Ok(Self::Equal(Equal::read_le(&mut reader)?)),
            6 => Ok(Self::Mul(Mul::read_le(&mut reader)?)),
            7 => Ok(Self::MulWrapped(MulWrapped::read_le(&mut reader)?)),
            8 => Ok(Self::Neg(Neg::read_le(&mut reader)?)),
            9 => Ok(Self::Not(Not::read_le(&mut reader)?)),
            10 => Ok(Self::Or(Or::read_le(&mut reader)?)),
            11 => Ok(Self::Sub(Sub::read_le(&mut reader)?)),
            12 => Ok(Self::SubWrapped(SubWrapped::read_le(&mut reader)?)),
            13 => Ok(Self::Xor(Xor::read_le(&mut reader)?)),
            14.. => Err(error(format!("Failed to deserialize an instruction of code {code}"))),
        }
    }
}

impl<P: Program> ToBytes for Instruction<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Add(instruction) => {
                u16::write_le(&0u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::AddWrapped(instruction) => {
                u16::write_le(&1u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::And(instruction) => {
                u16::write_le(&2u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Div(instruction) => {
                u16::write_le(&3u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::DivWrapped(instruction) => {
                u16::write_le(&4u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Equal(instruction) => {
                u16::write_le(&5u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Mul(instruction) => {
                u16::write_le(&6u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::MulWrapped(instruction) => {
                u16::write_le(&7u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Neg(instruction) => {
                u16::write_le(&8u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Not(instruction) => {
                u16::write_le(&1u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Or(instruction) => {
                u16::write_le(&1u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Sub(instruction) => {
                u16::write_le(&9u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::SubWrapped(instruction) => {
                u16::write_le(&10u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Xor(instruction) => {
                u16::write_le(&1u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[macro_export]
    macro_rules! test_instruction_halts {
        ($test_name:ident, $instruction: ident, $reason: expr, $a: expr, $b: expr) => {
            #[test]
            #[should_panic(expected = $reason)]
            fn $test_name() {
                use $crate::{
                    function::{Operation, Registers},
                    Parser,
                    Process,
                    Register,
                    Value,
                };
                type P = Process;

                let a = Value::<P>::from_str($a);
                let b = Value::<P>::from_str($b);

                let registers = Registers::<P>::default();
                registers.define(&Register::from_str("r0"));
                registers.define(&Register::from_str("r1"));
                registers.define(&Register::from_str("r2"));
                registers.assign(&Register::from_str("r0"), a);
                registers.assign(&Register::from_str("r1"), b);

                $instruction::from_str("r0 r1 into r2").evaluate(&registers);
            }
        };

        ($test_name:ident, $instruction: ident, $reason: expr, $input: expr) => {
            #[test]
            #[should_panic(expected = $reason)]
            fn $test_name() {
                use $crate::{
                    function::{Operation, Registers},
                    Parser,
                    Process,
                    Register,
                    Value,
                };
                type P = Process;

                let input = Value::<P>::from_str($input);

                let registers = Registers::<P>::default();
                registers.define(&Register::from_str("r0"));
                registers.define(&Register::from_str("r1"));
                registers.assign(&Register::from_str("r0"), input);

                $instruction::from_str("r0 into r1").evaluate(&registers);
            }
        };
    }

    #[macro_export]
    macro_rules! unary_instruction_test {
        ($test_name: ident, $instruction: ident, $input: expr, $expected: expr) => {
            #[test]
            fn $test_name() {
                use $crate::{
                    function::{Operation, Registers},
                    Parser,
                    Process,
                    Register,
                    Value,
                };
                type P = Process;

                let input = Value::<P>::from_str($input);
                let expected = Value::<P>::from_str($expected);

                let registers = Registers::<P>::default();
                registers.define(&Register::from_str("r0"));
                registers.define(&Register::from_str("r1"));
                registers.assign(&Register::from_str("r0"), input);

                $instruction::from_str("r0 into r1").evaluate(&registers);
                let candidate = registers.load(&Register::from_str("r1"));
                assert_eq!(expected, candidate);
            }
        };
    }

    #[macro_export]
    macro_rules! binary_instruction_test {
        ($test_name: ident, $instruction: ident, $a: expr, $b: expr, $c: expr) => {
            #[test]
            fn $test_name() {
                use $crate::{
                    function::{Operation, Registers},
                    Parser,
                    Process,
                    Register,
                    Value,
                };
                type P = Process;

                let a = Value::<P>::from_str($a);
                let b = Value::<P>::from_str($b);
                let expected = Value::<P>::from_str($c);

                let registers = Registers::<P>::default();
                registers.define(&Register::from_str("r0"));
                registers.define(&Register::from_str("r1"));
                registers.define(&Register::from_str("r2"));
                registers.assign(&Register::from_str("r0"), a);
                registers.assign(&Register::from_str("r1"), b);

                $instruction::from_str("r0 r1 into r2").evaluate(&registers);
                let candidate = registers.load(&Register::from_str("r2"));
                assert_eq!(expected, candidate);
            }
        };

        ($test_name: ident, $instruction: ident, $a: expr, $a_mode: expr, $b: expr, $b_mode: expr, $expected: expr, $expected_mode: expr) => {
            #[test]
            fn $test_name() {
                use $crate::{
                    function::{Operation, Registers},
                    Parser,
                    Process,
                    Register,
                    Value,
                };
                type P = Process;

                let a = Value::<P>::from_str(&format!("{}.{}", $a, $a_mode));
                let b = Value::<P>::from_str(&format!("{}.{}", $b, $b_mode));
                let expected = Value::<P>::from_str(&format!("{}.{}", $expected, $expected_mode));

                let registers = Registers::<P>::default();
                registers.define(&Register::from_str("r0"));
                registers.define(&Register::from_str("r1"));
                registers.define(&Register::from_str("r2"));
                registers.assign(&Register::from_str("r0"), a);
                registers.assign(&Register::from_str("r1"), b);

                $instruction::from_str("r0 r1 into r2").evaluate(&registers);
                let candidate = registers.load(&Register::from_str("r2"));
                assert_eq!(expected, candidate);
            }
        };
    }

    #[macro_export]
    macro_rules! test_modes_inner {
        ($type: ident, $instruction: ident, $a: expr, $b: expr, $expected: expr, $mode_tests: expr) => {
            use super::*;
            use $crate::binary_instruction_test;

            binary_instruction_test!(
                test_mode_0,
                $instruction,
                $a,
                $mode_tests[0][0],
                $b,
                $mode_tests[0][1],
                $expected,
                $mode_tests[0][2]
            );

            binary_instruction_test!(
                test_mode_1,
                $instruction,
                $a,
                $mode_tests[1][0],
                $b,
                $mode_tests[1][1],
                $expected,
                $mode_tests[1][2]
            );

            binary_instruction_test!(
                test_mode_2,
                $instruction,
                $a,
                $mode_tests[2][0],
                $b,
                $mode_tests[2][1],
                $expected,
                $mode_tests[2][2]
            );

            binary_instruction_test!(
                test_mode_3,
                $instruction,
                $a,
                $mode_tests[3][0],
                $b,
                $mode_tests[3][1],
                $expected,
                $mode_tests[3][2]
            );

            binary_instruction_test!(
                test_mode_4,
                $instruction,
                $a,
                $mode_tests[4][0],
                $b,
                $mode_tests[4][1],
                $expected,
                $mode_tests[4][2]
            );

            binary_instruction_test!(
                test_mode_5,
                $instruction,
                $a,
                $mode_tests[5][0],
                $b,
                $mode_tests[5][1],
                $expected,
                $mode_tests[5][2]
            );

            binary_instruction_test!(
                test_mode_6,
                $instruction,
                $a,
                $mode_tests[6][0],
                $b,
                $mode_tests[6][1],
                $expected,
                $mode_tests[6][2]
            );

            binary_instruction_test!(
                test_mode_7,
                $instruction,
                $a,
                $mode_tests[7][0],
                $b,
                $mode_tests[7][1],
                $expected,
                $mode_tests[7][2]
            );

            binary_instruction_test!(
                test_mode_8,
                $instruction,
                $a,
                $mode_tests[8][0],
                $b,
                $mode_tests[8][1],
                $expected,
                $mode_tests[8][2]
            );
        };
    }

    #[macro_export]
    macro_rules! test_modes {
        ($type: ident, $instruction: ident, $a: expr, $b: expr, $expected: expr) => {
            mod $type {
                use $crate::test_modes_inner;

                const DEFAULT_MODES: [[&str; 3]; 9] = [
                    ["public", "public", "private"],
                    ["public", "constant", "private"],
                    ["public", "private", "private"],
                    ["private", "constant", "private"],
                    ["private", "public", "private"],
                    ["private", "private", "private"],
                    ["constant", "private", "private"],
                    ["constant", "public", "private"],
                    ["constant", "constant", "constant"],
                ];

                test_modes_inner!($type, $instruction, $a, $b, $expected, DEFAULT_MODES);
            }
        };

        ($type: ident, $instruction: ident, $a: expr, $b: expr, $expected: expr, $modes: expr) => {
            mod $type {
                use $crate::test_modes_inner;

                test_modes_inner!($type, $instruction, $a, $b, $expected, $modes);
            }
        };

        ($type: ident, $instruction: ident, $input: expr, $expected: expr) => {
            mod $type {
                use super::*;
                use $crate::unary_instruction_test;

                unary_instruction_test!(
                    test_public_yields_private,
                    $instruction,
                    &format!("{}.public", $input),
                    &format!("{}.private", $expected)
                );

                unary_instruction_test!(
                    test_private_yields_private,
                    $instruction,
                    &format!("{}.private", $input),
                    &format!("{}.private", $expected)
                );

                unary_instruction_test!(
                    test_constant_yields_constant,
                    $instruction,
                    &format!("{}.constant", $input),
                    &format!("{}.constant", $expected)
                );
            }
        };
    }
}
