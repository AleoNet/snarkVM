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

#[macro_use]
mod boilerplate;

pub(super) mod add;
pub(super) use add::*;

pub(super) mod add_wrapped;
pub(super) use add_wrapped::*;

pub(super) mod commit;
pub(super) use commit::*;

pub(super) mod div;
pub(super) use div::*;

pub(super) mod div_wrapped;
pub(super) use div_wrapped::*;

pub(super) mod hash;
pub(super) use hash::*;

pub(super) mod mul;
pub(super) use mul::*;

pub(super) mod mul_wrapped;
pub(super) use mul_wrapped::*;

pub(super) mod neg;
pub(super) use neg::*;

pub(super) mod sub;
pub(super) use sub::*;

pub(super) mod sub_wrapped;
pub(super) use sub_wrapped::*;

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
    /// Performs a Pedersen commitment taking a 64-bit value as input.
    CommitPed64(CommitPed64<P>),
    /// Performs a Pedersen commitment taking a 128-bit value as input.
    CommitPed128(CommitPed128<P>),
    /// Performs a Pedersen commitment taking a 256-bit value as input.
    CommitPed256(CommitPed256<P>),
    /// Performs a Pedersen commitment taking a 512-bit value as input.
    CommitPed512(CommitPed512<P>),
    /// Performs a Pedersen commitment taking a 1024-bit value as input.
    CommitPed1024(CommitPed1024<P>),
    /// Divides `first` by `second`, storing the outcome in `destination`.
    Div(Div<P>),
    /// Divides `first` by `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    DivWrapped(DivWrapped<P>),
    /// Performs a Pedersen hash taking a 64-bit value as input.
    HashPed64(HashPed64<P>),
    /// Performs a Pedersen hash taking a 128-bit value as input.
    HashPed128(HashPed128<P>),
    /// Performs a Pedersen hash taking a 256-bit value as input.
    HashPed256(HashPed256<P>),
    /// Performs a Pedersen hash taking a 512-bit value as input.
    HashPed512(HashPed512<P>),
    /// Performs a Pedersen hash taking a 1024-bit value as input.
    HashPed1024(HashPed1024<P>),
    /// Performs a Poseidon hash with an input rate of 2.
    HashPsd2(HashPsd2<P>),
    /// Performs a Poseidon hash with an input rate of 4.
    HashPsd4(HashPsd4<P>),
    /// Performs a Poseidon hash with an input rate of 8.
    HashPsd8(HashPsd8<P>),
    /// Multiplies `first` with `second`, storing the outcome in `destination`.
    Mul(Mul<P>),
    /// Multiplies `first` with `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    MulWrapped(MulWrapped<P>),
    /// Negates `first`, storing the outcome in `destination`.
    Neg(Neg<P>),
    /// Subtracts `second` from `first`, storing the outcome in `destination`.
    Sub(Sub<P>),
    /// Subtracts `second` from `first`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    SubWrapped(SubWrapped<P>),
}

impl<P: Program> Instruction<P> {
    /// Returns the opcode of the instruction.
    #[inline]
    pub(crate) fn opcode(&self) -> &'static str {
        match self {
            Self::Add(..) => Add::<P>::opcode(),
            Self::AddWrapped(..) => AddWrapped::<P>::opcode(),
            Self::CommitPed64(..) => CommitPed64::<P>::opcode(),
            Self::CommitPed128(..) => CommitPed128::<P>::opcode(),
            Self::CommitPed256(..) => CommitPed256::<P>::opcode(),
            Self::CommitPed512(..) => CommitPed512::<P>::opcode(),
            Self::CommitPed1024(..) => CommitPed1024::<P>::opcode(),
            Self::HashPed64(..) => HashPed64::<P>::opcode(),
            Self::HashPed128(..) => HashPed128::<P>::opcode(),
            Self::HashPed256(..) => HashPed256::<P>::opcode(),
            Self::HashPed512(..) => HashPed512::<P>::opcode(),
            Self::HashPed1024(..) => HashPed1024::<P>::opcode(),
            Self::HashPsd2(..) => HashPsd2::<P>::opcode(),
            Self::HashPsd4(..) => HashPsd4::<P>::opcode(),
            Self::HashPsd8(..) => HashPsd8::<P>::opcode(),
            Self::Div(..) => Div::<P>::opcode(),
            Self::DivWrapped(..) => DivWrapped::<P>::opcode(),
            Self::Mul(..) => Mul::<P>::opcode(),
            Self::MulWrapped(..) => MulWrapped::<P>::opcode(),
            Self::Neg(..) => Neg::<P>::opcode(),
            Self::Sub(..) => Sub::<P>::opcode(),
            Self::SubWrapped(..) => SubWrapped::<P>::opcode(),
        }
    }

    /// Returns the operands of the instruction.
    #[inline]
    pub(crate) fn operands(&self) -> Vec<Operand<P>> {
        match self {
            Self::Add(add) => add.operands(),
            Self::AddWrapped(add_wrapped) => add_wrapped.operands(),
            Self::CommitPed64(ped64) => ped64.operands(),
            Self::CommitPed128(ped128) => ped128.operands(),
            Self::CommitPed256(ped256) => ped256.operands(),
            Self::CommitPed512(ped512) => ped512.operands(),
            Self::CommitPed1024(ped1024) => ped1024.operands(),
            Self::Div(div) => div.operands(),
            Self::DivWrapped(div_wrapped) => div_wrapped.operands(),
            Self::HashPed64(ped64) => ped64.operands(),
            Self::HashPed128(ped128) => ped128.operands(),
            Self::HashPed256(ped256) => ped256.operands(),
            Self::HashPed512(ped512) => ped512.operands(),
            Self::HashPed1024(ped1024) => ped1024.operands(),
            Self::HashPsd2(psd2) => psd2.operands(),
            Self::HashPsd4(psd4) => psd4.operands(),
            Self::HashPsd8(psd8) => psd8.operands(),
            Self::Mul(mul) => mul.operands(),
            Self::MulWrapped(mul_wrapped) => mul_wrapped.operands(),
            Self::Neg(neg) => neg.operands(),
            Self::Sub(sub) => sub.operands(),
            Self::SubWrapped(sub_wrapped) => sub_wrapped.operands(),
        }
    }

    /// Returns the destination register of the instruction.
    #[inline]
    pub(crate) fn destination(&self) -> &Register<P> {
        match self {
            Self::Add(add) => add.destination(),
            Self::AddWrapped(add_wrapped) => add_wrapped.destination(),
            Self::CommitPed64(ped64) => ped64.destination(),
            Self::CommitPed128(ped128) => ped128.destination(),
            Self::CommitPed256(ped256) => ped256.destination(),
            Self::CommitPed512(ped512) => ped512.destination(),
            Self::CommitPed1024(ped1024) => ped1024.destination(),
            Self::Div(div) => div.destination(),
            Self::DivWrapped(div_wrapped) => div_wrapped.destination(),
            Self::HashPed64(ped64) => ped64.destination(),
            Self::HashPed128(ped128) => ped128.destination(),
            Self::HashPed256(ped256) => ped256.destination(),
            Self::HashPed512(ped512) => ped512.destination(),
            Self::HashPed1024(ped1024) => ped1024.destination(),
            Self::HashPsd2(psd2) => psd2.destination(),
            Self::HashPsd4(psd4) => psd4.destination(),
            Self::HashPsd8(psd8) => psd8.destination(),
            Self::Mul(mul) => mul.destination(),
            Self::MulWrapped(mul_wrapped) => mul_wrapped.destination(),
            Self::Neg(neg) => neg.destination(),
            Self::Sub(sub) => sub.destination(),
            Self::SubWrapped(sub_wrapped) => sub_wrapped.destination(),
        }
    }

    /// Evaluates the instruction.
    #[inline]
    pub(crate) fn evaluate(&self, registers: &Registers<P>) {
        match self {
            Self::Add(instruction) => instruction.evaluate(registers),
            Self::AddWrapped(instruction) => instruction.evaluate(registers),
            Self::CommitPed64(instruction) => instruction.evaluate(registers),
            Self::CommitPed128(instruction) => instruction.evaluate(registers),
            Self::CommitPed256(instruction) => instruction.evaluate(registers),
            Self::CommitPed512(instruction) => instruction.evaluate(registers),
            Self::CommitPed1024(instruction) => instruction.evaluate(registers),
            Self::Div(instruction) => instruction.evaluate(registers),
            Self::DivWrapped(instruction) => instruction.evaluate(registers),
            Self::HashPed64(instruction) => instruction.evaluate(registers),
            Self::HashPed128(instruction) => instruction.evaluate(registers),
            Self::HashPed256(instruction) => instruction.evaluate(registers),
            Self::HashPed512(instruction) => instruction.evaluate(registers),
            Self::HashPed1024(instruction) => instruction.evaluate(registers),
            Self::HashPsd2(instruction) => instruction.evaluate(registers),
            Self::HashPsd4(instruction) => instruction.evaluate(registers),
            Self::HashPsd8(instruction) => instruction.evaluate(registers),
            Self::Mul(instruction) => instruction.evaluate(registers),
            Self::MulWrapped(instruction) => instruction.evaluate(registers),
            Self::Neg(instruction) => instruction.evaluate(registers),
            Self::Sub(instruction) => instruction.evaluate(registers),
            Self::SubWrapped(instruction) => instruction.evaluate(registers),
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
            preceded(pair(tag(CommitPed64::<P>::opcode()), tag(" ")), map(CommitPed64::parse, Into::into)),
            preceded(pair(tag(CommitPed128::<P>::opcode()), tag(" ")), map(CommitPed128::parse, Into::into)),
            preceded(pair(tag(CommitPed256::<P>::opcode()), tag(" ")), map(CommitPed256::parse, Into::into)),
            preceded(pair(tag(CommitPed512::<P>::opcode()), tag(" ")), map(CommitPed512::parse, Into::into)),
            preceded(pair(tag(CommitPed1024::<P>::opcode()), tag(" ")), map(CommitPed1024::parse, Into::into)),
            preceded(pair(tag(Div::<P>::opcode()), tag(" ")), map(Div::parse, Into::into)),
            preceded(pair(tag(DivWrapped::<P>::opcode()), tag(" ")), map(DivWrapped::parse, Into::into)),
            preceded(pair(tag(HashPed64::<P>::opcode()), tag(" ")), map(HashPed64::parse, Into::into)),
            preceded(pair(tag(HashPed128::<P>::opcode()), tag(" ")), map(HashPed128::parse, Into::into)),
            preceded(pair(tag(HashPed256::<P>::opcode()), tag(" ")), map(HashPed256::parse, Into::into)),
            preceded(pair(tag(HashPed512::<P>::opcode()), tag(" ")), map(HashPed512::parse, Into::into)),
            preceded(pair(tag(HashPed1024::<P>::opcode()), tag(" ")), map(HashPed1024::parse, Into::into)),
            preceded(pair(tag(HashPsd2::<P>::opcode()), tag(" ")), map(HashPsd2::parse, Into::into)),
            preceded(pair(tag(HashPsd4::<P>::opcode()), tag(" ")), map(HashPsd4::parse, Into::into)),
            preceded(pair(tag(HashPsd8::<P>::opcode()), tag(" ")), map(HashPsd8::parse, Into::into)),
            preceded(pair(tag(Mul::<P>::opcode()), tag(" ")), map(Mul::parse, Into::into)),
            preceded(pair(tag(MulWrapped::<P>::opcode()), tag(" ")), map(MulWrapped::parse, Into::into)),
            preceded(pair(tag(Neg::<P>::opcode()), tag(" ")), map(Neg::parse, Into::into)),
            // `alt` only takes a max of 21 parsers in a tuple, so we need to nest here.
            alt((
                preceded(pair(tag(Sub::<P>::opcode()), tag(" ")), map(Sub::parse, Into::into)),
                preceded(pair(tag(SubWrapped::<P>::opcode()), tag(" ")), map(SubWrapped::parse, Into::into)),
            )),
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
            Self::CommitPed64(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::CommitPed128(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::CommitPed256(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::CommitPed512(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::CommitPed1024(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Div(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::DivWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPed64(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPed128(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPed256(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPed512(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPed1024(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPsd2(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPsd4(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPsd8(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Mul(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::MulWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Neg(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Sub(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::SubWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
        }
    }
}

impl<P: Program> FromBytes for Instruction<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let code = u16::read_le(&mut reader)?;
        match code {
            0 => Ok(Self::Add(Add::read_le(&mut reader)?)),
            1 => Ok(Self::AddWrapped(AddWrapped::read_le(&mut reader)?)),
            2 => Ok(Self::CommitPed64(CommitPed64::read_le(&mut reader)?)),
            3 => Ok(Self::CommitPed128(CommitPed128::read_le(&mut reader)?)),
            4 => Ok(Self::CommitPed256(CommitPed256::read_le(&mut reader)?)),
            5 => Ok(Self::CommitPed512(CommitPed512::read_le(&mut reader)?)),
            6 => Ok(Self::CommitPed1024(CommitPed1024::read_le(&mut reader)?)),
            7 => Ok(Self::Div(Div::read_le(&mut reader)?)),
            8 => Ok(Self::DivWrapped(DivWrapped::read_le(&mut reader)?)),
            9 => Ok(Self::HashPed64(HashPed64::read_le(&mut reader)?)),
            10 => Ok(Self::HashPed128(HashPed128::read_le(&mut reader)?)),
            11 => Ok(Self::HashPed256(HashPed256::read_le(&mut reader)?)),
            12 => Ok(Self::HashPed512(HashPed512::read_le(&mut reader)?)),
            13 => Ok(Self::HashPed1024(HashPed1024::read_le(&mut reader)?)),
            14 => Ok(Self::HashPsd2(HashPsd2::read_le(&mut reader)?)),
            15 => Ok(Self::HashPsd4(HashPsd4::read_le(&mut reader)?)),
            16 => Ok(Self::HashPsd8(HashPsd8::read_le(&mut reader)?)),
            17 => Ok(Self::Mul(Mul::read_le(&mut reader)?)),
            18 => Ok(Self::MulWrapped(MulWrapped::read_le(&mut reader)?)),
            19 => Ok(Self::Neg(Neg::read_le(&mut reader)?)),
            20 => Ok(Self::Sub(Sub::read_le(&mut reader)?)),
            21 => Ok(Self::SubWrapped(SubWrapped::read_le(&mut reader)?)),
            22.. => Err(error(format!("Failed to deserialize an instruction of code {code}"))),
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
            Self::CommitPed64(instruction) => {
                u16::write_le(&2u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::CommitPed128(instruction) => {
                u16::write_le(&3u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::CommitPed256(instruction) => {
                u16::write_le(&4u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::CommitPed512(instruction) => {
                u16::write_le(&5u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::CommitPed1024(instruction) => {
                u16::write_le(&6u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Div(instruction) => {
                u16::write_le(&7u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::DivWrapped(instruction) => {
                u16::write_le(&8u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPed64(instruction) => {
                u16::write_le(&9u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPed128(instruction) => {
                u16::write_le(&10u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPed256(instruction) => {
                u16::write_le(&11u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPed512(instruction) => {
                u16::write_le(&12u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPed1024(instruction) => {
                u16::write_le(&13u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPsd2(instruction) => {
                u16::write_le(&14u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPsd4(instruction) => {
                u16::write_le(&15u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPsd8(instruction) => {
                u16::write_le(&16u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Mul(instruction) => {
                u16::write_le(&17u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::MulWrapped(instruction) => {
                u16::write_le(&18u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Neg(instruction) => {
                u16::write_le(&19u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Sub(instruction) => {
                u16::write_le(&20u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::SubWrapped(instruction) => {
                u16::write_le(&21u16, &mut writer)?;
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
    }

    #[macro_export]
    macro_rules! test_modes {
        ($type: ident, $instruction: ident, $a: expr, $b: expr, $expected: expr) => {
            mod $type {
                use super::*;
                use $crate::binary_instruction_test;

                binary_instruction_test!(
                    test_public_and_public_yields_private,
                    $instruction,
                    &format!("{}.public", $a),
                    &format!("{}.public", $b),
                    &format!("{}.private", $expected)
                );

                binary_instruction_test!(
                    test_public_and_constant_yields_private,
                    $instruction,
                    &format!("{}.public", $a),
                    &format!("{}.constant", $b),
                    &format!("{}.private", $expected)
                );

                binary_instruction_test!(
                    test_public_and_private_yields_private,
                    $instruction,
                    &format!("{}.public", $a),
                    &format!("{}.private", $b),
                    &format!("{}.private", $expected)
                );

                binary_instruction_test!(
                    test_private_and_constant_yields_private,
                    $instruction,
                    &format!("{}.private", $a),
                    &format!("{}.constant", $b),
                    &format!("{}.private", $expected)
                );

                binary_instruction_test!(
                    test_private_and_public_yields_private,
                    $instruction,
                    &format!("{}.private", $a),
                    &format!("{}.public", $b),
                    &format!("{}.private", $expected)
                );

                binary_instruction_test!(
                    test_private_and_private_yields_private,
                    $instruction,
                    &format!("{}.private", $a),
                    &format!("{}.private", $b),
                    &format!("{}.private", $expected)
                );

                binary_instruction_test!(
                    test_constant_and_private_yields_private,
                    $instruction,
                    &format!("{}.constant", $a),
                    &format!("{}.private", $b),
                    &format!("{}.private", $expected)
                );

                binary_instruction_test!(
                    test_constant_and_public_yields_private,
                    $instruction,
                    &format!("{}.constant", $a),
                    &format!("{}.public", $b),
                    &format!("{}.private", $expected)
                );

                binary_instruction_test!(
                    test_constant_and_constant_yields_constant,
                    $instruction,
                    &format!("{}.constant", $a),
                    &format!("{}.constant", $b),
                    &format!("{}.constant", $expected)
                );
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
