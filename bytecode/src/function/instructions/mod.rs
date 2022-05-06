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

pub(super) mod abs;
pub(super) use abs::*;

pub(super) mod abs_wrapped;
pub(super) use abs_wrapped::*;

pub(super) mod add;
pub(super) use add::*;

pub(super) mod and;
pub(super) use and::*;

pub(super) mod add_wrapped;
pub(super) use add_wrapped::*;

pub(super) mod commit;
pub(super) use commit::*;

pub(super) mod div;
pub(super) use div::*;

pub(super) mod div_wrapped;
pub(super) use div_wrapped::*;

pub(super) mod double;
pub(super) use double::*;

pub(super) mod equal;
pub(super) use equal::*;

pub(super) mod gt;
pub(super) use gt::*;

pub(super) mod ge;
pub(super) use ge::*;

pub(super) mod hash;
pub(super) use hash::*;

pub(super) mod inv;
pub(super) use inv::*;

pub(super) mod lt;
pub(super) use lt::*;

pub(super) mod le;
pub(super) use le::*;

pub(super) mod mul;
pub(super) use mul::*;

pub(super) mod mul_wrapped;
pub(super) use mul_wrapped::*;

pub(super) mod nand;
pub(super) use nand::*;

pub(super) mod neg;
pub(super) use neg::*;

pub(super) mod nor;
pub(super) use nor::*;

pub(super) mod not;
pub(super) use not::*;

pub(super) mod not_equal;
pub(super) use not_equal::*;

pub(super) mod or;
pub(super) use or::*;

pub(super) mod pow;
pub(super) use pow::*;

pub(super) mod pow_wrapped;
pub(super) use pow_wrapped::*;

pub(super) mod square;
pub(super) use square::*;

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
    /// Compute the absolute value of `first`, checking for overflow, and storing the outcome in `destination`.
    Abs(Abs<P>),
    /// Compute the absolute value of `first`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    AbsWrapped(AbsWrapped<P>),
    /// Adds `first` with `second`, storing the outcome in `destination`.
    Add(Add<P>),
    /// Adds `first` with `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    AddWrapped(AddWrapped<P>),
    /// Performs a bitwise AND operation on `first` and `second`, storing the outcome in `destination`.
    And(And<P>),
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
    /// Doubles `first`, storing the outcome in `destination`.
    Double(Double<P>),
    /// Checks if `first` is equal to `second`, storing the outcome in `destination`.
    Equal(Equal<P>),
    /// Checks if `first` is greater than `second`, storing the result in `destination`.
    GreaterThan(GreaterThan<P>),
    /// Checks if `first` is greater than or equal to `second`, storing the result in `destination`.
    GreaterThanOrEqual(GreaterThanOrEqual<P>),
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
    /// Computes the multiplicative inverse of `first`, storing the outcome in `destination`.
    Inv(Inv<P>),
    /// Checks if `first` is less than `second`, storing the outcome in `destination`.
    LessThan(LessThan<P>),
    /// Checks if `first` is less than or equal to `second`, storing the outcome in `destination`.
    LessThanOrEqual(LessThanOrEqual<P>),
    /// Multiplies `first` with `second`, storing the outcome in `destination`.
    Mul(Mul<P>),
    /// Multiplies `first` with `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    MulWrapped(MulWrapped<P>),
    /// Returns false only if `first` and `second` are true, storing the outcome in `destination`.
    Nand(Nand<P>),
    /// Negates `first`, storing the outcome in `destination`.
    Neg(Neg<P>),
    /// Returns true when neither `first` nor `second` is true, storing the outcome in `destination`.
    Nor(Nor<P>),
    /// Flips each bit in the representation of `first`, storing the outcome in `destination`.
    Not(Not<P>),
    /// Returns true if `first` is not equal to `second`, storing the result in `destination`.
    NotEqual(NotEqual<P>),
    /// Performs a bitwise Or on `first` and `second`, storing the outcome in `destination`.
    Or(Or<P>),
    /// Raises `first` to the power of `second`, storing the outcome in `destination`.
    Pow(Pow<P>),
    /// Raises `first` to the power of `second`, wrapping around at the boundary of the type, storing the outcome in `destination`.
    PowWrapped(PowWrapped<P>),
    /// Squares 'first', storing the outcome in `destination`.
    Square(Square<P>),
    /// Computes `first - second`, storing the outcome in `destination`.
    Sub(Sub<P>),
    /// Computes `first - second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    SubWrapped(SubWrapped<P>),
    /// Performs a bitwise Xor on `first` and `second`, storing the outcome in `destination`.
    Xor(Xor<P>),
}

impl<P: Program> Instruction<P> {
    /// Returns the opcode of the instruction.
    #[inline]
    pub(crate) fn opcode(&self) -> &'static str {
        match self {
            Self::Abs(..) => Abs::<P>::opcode(),
            Self::AbsWrapped(..) => AbsWrapped::<P>::opcode(),
            Self::Add(..) => Add::<P>::opcode(),
            Self::AddWrapped(..) => AddWrapped::<P>::opcode(),
            Self::And(..) => And::<P>::opcode(),
            Self::CommitPed64(..) => CommitPed64::<P>::opcode(),
            Self::CommitPed128(..) => CommitPed128::<P>::opcode(),
            Self::CommitPed256(..) => CommitPed256::<P>::opcode(),
            Self::CommitPed512(..) => CommitPed512::<P>::opcode(),
            Self::CommitPed1024(..) => CommitPed1024::<P>::opcode(),
            Self::Div(..) => Div::<P>::opcode(),
            Self::DivWrapped(..) => DivWrapped::<P>::opcode(),
            Self::Double(..) => Double::<P>::opcode(),
            Self::Equal(..) => Equal::<P>::opcode(),
            Self::GreaterThan(..) => GreaterThan::<P>::opcode(),
            Self::GreaterThanOrEqual(..) => GreaterThanOrEqual::<P>::opcode(),
            Self::HashPed64(..) => HashPed64::<P>::opcode(),
            Self::HashPed128(..) => HashPed128::<P>::opcode(),
            Self::HashPed256(..) => HashPed256::<P>::opcode(),
            Self::HashPed512(..) => HashPed512::<P>::opcode(),
            Self::HashPed1024(..) => HashPed1024::<P>::opcode(),
            Self::HashPsd2(..) => HashPsd2::<P>::opcode(),
            Self::HashPsd4(..) => HashPsd4::<P>::opcode(),
            Self::HashPsd8(..) => HashPsd8::<P>::opcode(),
            Self::Inv(..) => Inv::<P>::opcode(),
            Self::LessThan(..) => LessThan::<P>::opcode(),
            Self::LessThanOrEqual(..) => LessThanOrEqual::<P>::opcode(),
            Self::Mul(..) => Mul::<P>::opcode(),
            Self::MulWrapped(..) => MulWrapped::<P>::opcode(),
            Self::Nand(..) => Nand::<P>::opcode(),
            Self::Neg(..) => Neg::<P>::opcode(),
            Self::Nor(..) => Nor::<P>::opcode(),
            Self::Not(..) => Not::<P>::opcode(),
            Self::NotEqual(..) => NotEqual::<P>::opcode(),
            Self::Or(..) => Or::<P>::opcode(),
            Self::Pow(..) => Pow::<P>::opcode(),
            Self::PowWrapped(..) => PowWrapped::<P>::opcode(),
            Self::Square(..) => Square::<P>::opcode(),
            Self::Sub(..) => Sub::<P>::opcode(),
            Self::SubWrapped(..) => SubWrapped::<P>::opcode(),
            Self::Xor(..) => Xor::<P>::opcode(),
        }
    }

    /// Returns the operands of the instruction.
    #[inline]
    pub(crate) fn operands(&self) -> Vec<Operand<P>> {
        match self {
            Self::Abs(abs) => abs.operands(),
            Self::AbsWrapped(abs) => abs.operands(),
            Self::Add(add) => add.operands(),
            Self::AddWrapped(add_wrapped) => add_wrapped.operands(),
            Self::And(and) => and.operands(),
            Self::CommitPed64(ped64) => ped64.operands(),
            Self::CommitPed128(ped128) => ped128.operands(),
            Self::CommitPed256(ped256) => ped256.operands(),
            Self::CommitPed512(ped512) => ped512.operands(),
            Self::CommitPed1024(ped1024) => ped1024.operands(),
            Self::Div(div) => div.operands(),
            Self::DivWrapped(div_wrapped) => div_wrapped.operands(),
            Self::Double(double) => double.operands(),
            Self::Equal(equal) => equal.operands(),
            Self::GreaterThan(greater_than) => greater_than.operands(),
            Self::GreaterThanOrEqual(greater_than_or_equal) => greater_than_or_equal.operands(),
            Self::HashPed64(ped64) => ped64.operands(),
            Self::HashPed128(ped128) => ped128.operands(),
            Self::HashPed256(ped256) => ped256.operands(),
            Self::HashPed512(ped512) => ped512.operands(),
            Self::HashPed1024(ped1024) => ped1024.operands(),
            Self::HashPsd2(psd2) => psd2.operands(),
            Self::HashPsd4(psd4) => psd4.operands(),
            Self::HashPsd8(psd8) => psd8.operands(),
            Self::Inv(inv) => inv.operands(),
            Self::LessThan(less_than) => less_than.operands(),
            Self::LessThanOrEqual(less_than_or_equal) => less_than_or_equal.operands(),
            Self::Mul(mul) => mul.operands(),
            Self::MulWrapped(mul_wrapped) => mul_wrapped.operands(),
            Self::Nand(nand) => nand.operands(),
            Self::Neg(neg) => neg.operands(),
            Self::Nor(nor) => nor.operands(),
            Self::Not(not) => not.operands(),
            Self::NotEqual(not_equal) => not_equal.operands(),
            Self::Or(or) => or.operands(),
            Self::Pow(pow) => pow.operands(),
            Self::PowWrapped(pow_wrapped) => pow_wrapped.operands(),
            Self::Square(square) => square.operands(),
            Self::Sub(sub) => sub.operands(),
            Self::SubWrapped(sub_wrapped) => sub_wrapped.operands(),
            Self::Xor(xor) => xor.operands(),
        }
    }

    /// Returns the destination register of the instruction.
    #[inline]
    pub(crate) fn destination(&self) -> &Register<P> {
        match self {
            Self::Abs(abs) => abs.destination(),
            Self::AbsWrapped(abs) => abs.destination(),
            Self::Add(add) => add.destination(),
            Self::AddWrapped(add_wrapped) => add_wrapped.destination(),
            Self::And(and) => and.destination(),
            Self::CommitPed64(ped64) => ped64.destination(),
            Self::CommitPed128(ped128) => ped128.destination(),
            Self::CommitPed256(ped256) => ped256.destination(),
            Self::CommitPed512(ped512) => ped512.destination(),
            Self::CommitPed1024(ped1024) => ped1024.destination(),
            Self::Div(div) => div.destination(),
            Self::DivWrapped(div_wrapped) => div_wrapped.destination(),
            Self::Double(double) => double.destination(),
            Self::Equal(equal) => equal.destination(),
            Self::GreaterThan(greater_than) => greater_than.destination(),
            Self::GreaterThanOrEqual(greater_than_or_equal) => greater_than_or_equal.destination(),
            Self::HashPed64(ped64) => ped64.destination(),
            Self::HashPed128(ped128) => ped128.destination(),
            Self::HashPed256(ped256) => ped256.destination(),
            Self::HashPed512(ped512) => ped512.destination(),
            Self::HashPed1024(ped1024) => ped1024.destination(),
            Self::HashPsd2(psd2) => psd2.destination(),
            Self::HashPsd4(psd4) => psd4.destination(),
            Self::HashPsd8(psd8) => psd8.destination(),
            Self::Inv(inv) => inv.destination(),
            Self::LessThan(less_than) => less_than.destination(),
            Self::LessThanOrEqual(less_than_or_equal) => less_than_or_equal.destination(),
            Self::Mul(mul) => mul.destination(),
            Self::MulWrapped(mul_wrapped) => mul_wrapped.destination(),
            Self::Nand(nand) => nand.destination(),
            Self::Neg(neg) => neg.destination(),
            Self::Nor(nor) => nor.destination(),
            Self::Not(not) => not.destination(),
            Self::NotEqual(not_equal) => not_equal.destination(),
            Self::Or(or) => or.destination(),
            Self::Pow(pow) => pow.destination(),
            Self::PowWrapped(pow_wrapped) => pow_wrapped.destination(),
            Self::Square(square) => square.destination(),
            Self::Sub(sub) => sub.destination(),
            Self::SubWrapped(sub_wrapped) => sub_wrapped.destination(),
            Self::Xor(xor) => xor.destination(),
        }
    }

    /// Evaluates the instruction.
    #[inline]
    pub(crate) fn evaluate(&self, registers: &Registers<P>) {
        match self {
            Self::Abs(abs) => abs.evaluate(registers),
            Self::AbsWrapped(abs) => abs.evaluate(registers),
            Self::Add(instruction) => instruction.evaluate(registers),
            Self::AddWrapped(instruction) => instruction.evaluate(registers),
            Self::And(instruction) => instruction.evaluate(registers),
            Self::CommitPed64(instruction) => instruction.evaluate(registers),
            Self::CommitPed128(instruction) => instruction.evaluate(registers),
            Self::CommitPed256(instruction) => instruction.evaluate(registers),
            Self::CommitPed512(instruction) => instruction.evaluate(registers),
            Self::CommitPed1024(instruction) => instruction.evaluate(registers),
            Self::Div(instruction) => instruction.evaluate(registers),
            Self::DivWrapped(instruction) => instruction.evaluate(registers),
            Self::Double(instruction) => instruction.evaluate(registers),
            Self::Equal(instruction) => instruction.evaluate(registers),
            Self::GreaterThan(instruction) => instruction.evaluate(registers),
            Self::GreaterThanOrEqual(instruction) => instruction.evaluate(registers),
            Self::HashPed64(instruction) => instruction.evaluate(registers),
            Self::HashPed128(instruction) => instruction.evaluate(registers),
            Self::HashPed256(instruction) => instruction.evaluate(registers),
            Self::HashPed512(instruction) => instruction.evaluate(registers),
            Self::HashPed1024(instruction) => instruction.evaluate(registers),
            Self::HashPsd2(instruction) => instruction.evaluate(registers),
            Self::HashPsd4(instruction) => instruction.evaluate(registers),
            Self::HashPsd8(instruction) => instruction.evaluate(registers),
            Self::Inv(instruction) => instruction.evaluate(registers),
            Self::LessThan(instruction) => instruction.evaluate(registers),
            Self::LessThanOrEqual(instruction) => instruction.evaluate(registers),
            Self::Mul(instruction) => instruction.evaluate(registers),
            Self::MulWrapped(instruction) => instruction.evaluate(registers),
            Self::Nand(instruction) => instruction.evaluate(registers),
            Self::Neg(instruction) => instruction.evaluate(registers),
            Self::Nor(instruction) => instruction.evaluate(registers),
            Self::Not(instruction) => instruction.evaluate(registers),
            Self::NotEqual(instruction) => instruction.evaluate(registers),
            Self::Or(instruction) => instruction.evaluate(registers),
            Self::Pow(instruction) => instruction.evaluate(registers),
            Self::PowWrapped(instruction) => instruction.evaluate(registers),
            Self::Square(instruction) => instruction.evaluate(registers),
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
            // nom documentation notes that alt supports a maximum of 21 parsers.
            // The documentation suggests to nest alt to support more parsers, as we do here.
            // Note that order of the individual parsers matters.
            alt((
                alt((
                    preceded(pair(tag(Abs::<P>::opcode()), tag(" ")), map(Abs::parse, Into::into)),
                    preceded(pair(tag(AbsWrapped::<P>::opcode()), tag(" ")), map(AbsWrapped::parse, Into::into)),
                    preceded(pair(tag(Add::<P>::opcode()), tag(" ")), map(Add::parse, Into::into)),
                    preceded(pair(tag(AddWrapped::<P>::opcode()), tag(" ")), map(AddWrapped::parse, Into::into)),
                    preceded(pair(tag(And::<P>::opcode()), tag(" ")), map(And::parse, Into::into)),
                    preceded(pair(tag(CommitPed64::<P>::opcode()), tag(" ")), map(CommitPed64::parse, Into::into)),
                    preceded(pair(tag(CommitPed128::<P>::opcode()), tag(" ")), map(CommitPed128::parse, Into::into)),
                    preceded(pair(tag(CommitPed256::<P>::opcode()), tag(" ")), map(CommitPed256::parse, Into::into)),
                    preceded(pair(tag(CommitPed512::<P>::opcode()), tag(" ")), map(CommitPed512::parse, Into::into)),
                    preceded(pair(tag(CommitPed1024::<P>::opcode()), tag(" ")), map(CommitPed1024::parse, Into::into)),
                    preceded(pair(tag(Div::<P>::opcode()), tag(" ")), map(Div::parse, Into::into)),
                    preceded(pair(tag(DivWrapped::<P>::opcode()), tag(" ")), map(DivWrapped::parse, Into::into)),
                    preceded(pair(tag(Double::<P>::opcode()), tag(" ")), map(Double::parse, Into::into)),
                    preceded(pair(tag(Equal::<P>::opcode()), tag(" ")), map(Equal::parse, Into::into)),
                    preceded(pair(tag(GreaterThan::<P>::opcode()), tag(" ")), map(GreaterThan::parse, Into::into)),
                    preceded(
                        pair(tag(GreaterThanOrEqual::<P>::opcode()), tag(" ")),
                        map(GreaterThanOrEqual::parse, Into::into),
                    ),
                    preceded(pair(tag(HashPed64::<P>::opcode()), tag(" ")), map(HashPed64::parse, Into::into)),
                    preceded(pair(tag(HashPed128::<P>::opcode()), tag(" ")), map(HashPed128::parse, Into::into)),
                    preceded(pair(tag(HashPed256::<P>::opcode()), tag(" ")), map(HashPed256::parse, Into::into)),
                    preceded(pair(tag(HashPed512::<P>::opcode()), tag(" ")), map(HashPed512::parse, Into::into)),
                    preceded(pair(tag(HashPed1024::<P>::opcode()), tag(" ")), map(HashPed1024::parse, Into::into)),
                )),
                preceded(pair(tag(HashPsd2::<P>::opcode()), tag(" ")), map(HashPsd2::parse, Into::into)),
                preceded(pair(tag(HashPsd4::<P>::opcode()), tag(" ")), map(HashPsd4::parse, Into::into)),
                preceded(pair(tag(HashPsd8::<P>::opcode()), tag(" ")), map(HashPsd8::parse, Into::into)),
                preceded(pair(tag(Inv::<P>::opcode()), tag(" ")), map(Inv::parse, Into::into)),
                preceded(pair(tag(LessThan::<P>::opcode()), tag(" ")), map(LessThan::parse, Into::into)),
                preceded(pair(tag(LessThanOrEqual::<P>::opcode()), tag(" ")), map(LessThanOrEqual::parse, Into::into)),
                preceded(pair(tag(Mul::<P>::opcode()), tag(" ")), map(Mul::parse, Into::into)),
                preceded(pair(tag(MulWrapped::<P>::opcode()), tag(" ")), map(MulWrapped::parse, Into::into)),
                preceded(pair(tag(Nand::<P>::opcode()), tag(" ")), map(Nand::parse, Into::into)),
                preceded(pair(tag(Neg::<P>::opcode()), tag(" ")), map(Neg::parse, Into::into)),
                preceded(pair(tag(Nor::<P>::opcode()), tag(" ")), map(Nor::parse, Into::into)),
                preceded(pair(tag(Not::<P>::opcode()), tag(" ")), map(Not::parse, Into::into)),
                preceded(pair(tag(NotEqual::<P>::opcode()), tag(" ")), map(NotEqual::parse, Into::into)),
                preceded(pair(tag(Or::<P>::opcode()), tag(" ")), map(Or::parse, Into::into)),
                preceded(pair(tag(Pow::<P>::opcode()), tag(" ")), map(Pow::parse, Into::into)),
                preceded(pair(tag(PowWrapped::<P>::opcode()), tag(" ")), map(PowWrapped::parse, Into::into)),
                preceded(pair(tag(Square::<P>::opcode()), tag(" ")), map(Square::parse, Into::into)),
                preceded(pair(tag(Sub::<P>::opcode()), tag(" ")), map(Sub::parse, Into::into)),
                preceded(pair(tag(SubWrapped::<P>::opcode()), tag(" ")), map(SubWrapped::parse, Into::into)),
                preceded(pair(tag(Xor::<P>::opcode()), tag(" ")), map(Xor::parse, Into::into)),
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
            Self::Abs(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::AbsWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Add(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::AddWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::And(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::CommitPed64(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::CommitPed128(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::CommitPed256(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::CommitPed512(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::CommitPed1024(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Div(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::DivWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Double(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Equal(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::GreaterThan(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::GreaterThanOrEqual(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPed64(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPed128(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPed256(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPed512(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPed1024(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPsd2(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPsd4(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::HashPsd8(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Inv(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::LessThan(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::LessThanOrEqual(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Mul(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::MulWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Nand(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Neg(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Nor(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Not(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::NotEqual(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Or(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Pow(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::PowWrapped(instruction) => write!(f, "{} {};", self.opcode(), instruction),
            Self::Square(instruction) => write!(f, "{} {};", self.opcode(), instruction),
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
            0 => Ok(Self::Abs(Abs::read_le(&mut reader)?)),
            1 => Ok(Self::AbsWrapped(AbsWrapped::read_le(&mut reader)?)),
            2 => Ok(Self::Add(Add::read_le(&mut reader)?)),
            3 => Ok(Self::AddWrapped(AddWrapped::read_le(&mut reader)?)),
            4 => Ok(Self::And(And::read_le(&mut reader)?)),
            5 => Ok(Self::CommitPed64(CommitPed64::read_le(&mut reader)?)),
            6 => Ok(Self::CommitPed128(CommitPed128::read_le(&mut reader)?)),
            7 => Ok(Self::CommitPed256(CommitPed256::read_le(&mut reader)?)),
            8 => Ok(Self::CommitPed512(CommitPed512::read_le(&mut reader)?)),
            9 => Ok(Self::CommitPed1024(CommitPed1024::read_le(&mut reader)?)),
            10 => Ok(Self::Div(Div::read_le(&mut reader)?)),
            11 => Ok(Self::DivWrapped(DivWrapped::read_le(&mut reader)?)),
            12 => Ok(Self::Double(Double::read_le(&mut reader)?)),
            13 => Ok(Self::Equal(Equal::read_le(&mut reader)?)),
            14 => Ok(Self::GreaterThan(GreaterThan::read_le(&mut reader)?)),
            15 => Ok(Self::GreaterThanOrEqual(GreaterThanOrEqual::read_le(&mut reader)?)),
            16 => Ok(Self::HashPed64(HashPed64::read_le(&mut reader)?)),
            17 => Ok(Self::HashPed128(HashPed128::read_le(&mut reader)?)),
            18 => Ok(Self::HashPed256(HashPed256::read_le(&mut reader)?)),
            19 => Ok(Self::HashPed512(HashPed512::read_le(&mut reader)?)),
            20 => Ok(Self::HashPed1024(HashPed1024::read_le(&mut reader)?)),
            21 => Ok(Self::HashPsd2(HashPsd2::read_le(&mut reader)?)),
            22 => Ok(Self::HashPsd4(HashPsd4::read_le(&mut reader)?)),
            23 => Ok(Self::HashPsd8(HashPsd8::read_le(&mut reader)?)),
            24 => Ok(Self::Inv(Inv::read_le(&mut reader)?)),
            25 => Ok(Self::LessThan(LessThan::read_le(&mut reader)?)),
            26 => Ok(Self::LessThanOrEqual(LessThanOrEqual::read_le(&mut reader)?)),
            27 => Ok(Self::Mul(Mul::read_le(&mut reader)?)),
            28 => Ok(Self::MulWrapped(MulWrapped::read_le(&mut reader)?)),
            29 => Ok(Self::Nand(Nand::read_le(&mut reader)?)),
            30 => Ok(Self::Neg(Neg::read_le(&mut reader)?)),
            31 => Ok(Self::Nor(Nor::read_le(&mut reader)?)),
            32 => Ok(Self::Not(Not::read_le(&mut reader)?)),
            33 => Ok(Self::NotEqual(NotEqual::read_le(&mut reader)?)),
            34 => Ok(Self::Or(Or::read_le(&mut reader)?)),
            35 => Ok(Self::Pow(Pow::read_le(&mut reader)?)),
            36 => Ok(Self::PowWrapped(PowWrapped::read_le(&mut reader)?)),
            37 => Ok(Self::Square(Square::read_le(&mut reader)?)),
            38 => Ok(Self::Sub(Sub::read_le(&mut reader)?)),
            39 => Ok(Self::SubWrapped(SubWrapped::read_le(&mut reader)?)),
            40 => Ok(Self::Xor(Xor::read_le(&mut reader)?)),
            41.. => Err(error(format!("Failed to deserialize an instruction of code {code}"))),
        }
    }
}

impl<P: Program> ToBytes for Instruction<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Abs(instruction) => {
                u16::write_le(&0u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::AbsWrapped(instruction) => {
                u16::write_le(&1u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Add(instruction) => {
                u16::write_le(&2u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::AddWrapped(instruction) => {
                u16::write_le(&3u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::And(instruction) => {
                u16::write_le(&4u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::CommitPed64(instruction) => {
                u16::write_le(&3u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::CommitPed128(instruction) => {
                u16::write_le(&4u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::CommitPed256(instruction) => {
                u16::write_le(&5u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::CommitPed512(instruction) => {
                u16::write_le(&6u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::CommitPed1024(instruction) => {
                u16::write_le(&7u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Div(instruction) => {
                u16::write_le(&5u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::DivWrapped(instruction) => {
                u16::write_le(&6u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Double(instruction) => {
                u16::write_le(&7u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Equal(instruction) => {
                u16::write_le(&8u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::GreaterThan(instruction) => {
                u16::write_le(&9u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::GreaterThanOrEqual(instruction) => {
                u16::write_le(&10u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPed64(instruction) => {
                u16::write_le(&13u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPed128(instruction) => {
                u16::write_le(&14u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPed256(instruction) => {
                u16::write_le(&15u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPed512(instruction) => {
                u16::write_le(&16u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPed1024(instruction) => {
                u16::write_le(&17u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPsd2(instruction) => {
                u16::write_le(&18u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPsd4(instruction) => {
                u16::write_le(&19u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::HashPsd8(instruction) => {
                u16::write_le(&20u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Inv(instruction) => {
                u16::write_le(&11u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::LessThan(instruction) => {
                u16::write_le(&12u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::LessThanOrEqual(instruction) => {
                u16::write_le(&13u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Mul(instruction) => {
                u16::write_le(&14u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::MulWrapped(instruction) => {
                u16::write_le(&15u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Nand(instruction) => {
                u16::write_le(&16u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Neg(instruction) => {
                u16::write_le(&17u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Nor(instruction) => {
                u16::write_le(&18u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Not(instruction) => {
                u16::write_le(&19u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::NotEqual(instruction) => {
                u16::write_le(&20u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Or(instruction) => {
                u16::write_le(&21u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Pow(instruction) => {
                u16::write_le(&22u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::PowWrapped(instruction) => {
                u16::write_le(&23u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Square(instruction) => {
                u16::write_le(&24u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Sub(instruction) => {
                u16::write_le(&25u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::SubWrapped(instruction) => {
                u16::write_le(&26u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
            Self::Xor(instruction) => {
                u16::write_le(&27u16, &mut writer)?;
                instruction.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        function::{instructions::Opcode, Operation, Registers},
        Parser,
        Process,
        Register,
        Value,
    };

    type P = Process;

    pub fn test_binary<Op: Operation<P> + Opcode>(a_str: &str, b_str: &str, expected_str: &str) {
        let a = Value::<P>::from_str(a_str);
        let b = Value::<P>::from_str(b_str);
        let expected = Value::<P>::from_str(expected_str);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.define(&Register::from_str("r2"));
        registers.assign(&Register::from_str("r0"), a);
        registers.assign(&Register::from_str("r1"), b);

        Op::from_str("r0 r1 into r2").evaluate(&registers);
        let candidate = registers.load(&Register::from_str("r2"));
        assert_eq!(
            expected,
            candidate,
            "Expected '{} {} {}' to output {} but got {}",
            Op::opcode(),
            a_str,
            b_str,
            expected_str,
            candidate
        );
    }

    pub fn test_unary<Op: Operation<P> + Opcode>(input_str: &str, expected_str: &str) {
        let input = Value::<P>::from_str(input_str);
        let expected = Value::<P>::from_str(expected_str);

        let registers = Registers::<P>::default();
        registers.define(&Register::from_str("r0"));
        registers.define(&Register::from_str("r1"));
        registers.assign(&Register::from_str("r0"), input);

        Op::from_str("r0 into r1").evaluate(&registers);
        let candidate = registers.load(&Register::from_str("r1"));
        assert_eq!(
            expected,
            candidate,
            "Expected '{} {}' to output {} but got {}",
            Op::opcode(),
            input_str,
            expected_str,
            candidate
        );
    }

    #[macro_export]
    macro_rules! test_instruction_halts {
        ($test_name:ident, $operation: ident, $reason: expr, $a: expr, $b: expr) => {
            #[test]
            #[should_panic(expected = $reason)]
            fn $test_name() {
                use $crate::{function::instructions::tests::test_binary, Process};
                test_binary::<$operation<Process>>($a, $b, "\"Unreachable\"");
            }
        };

        ($test_name:ident, $operation: ident, $reason: expr, $input: expr) => {
            #[test]
            #[should_panic(expected = $reason)]
            fn $test_name() {
                use $crate::{function::instructions::tests::test_unary, Process};
                test_unary::<$operation<Process>>($input, "\"Unreachable\"");
            }
        };
    }

    #[macro_export]
    macro_rules! unary_instruction_test {
        ($test_name:ident, $operation: ident, $input:expr, $expected:expr) => {
            #[test]
            fn $test_name() {
                use $crate::{function::instructions::tests::test_unary, Process};
                test_unary::<$operation<Process>>($input, $expected);
            }
        };
    }

    #[macro_export]
    macro_rules! binary_instruction_test {
        ($test_name:ident, $operation: ident, $a:expr, $b:expr, $expected:expr) => {
            #[test]
            fn $test_name() {
                use $crate::{function::instructions::tests::test_binary, Process};
                test_binary::<$operation<Process>>($a, $b, $expected);
            }
        };
    }

    #[macro_export]
    macro_rules! test_modes {
        ($type: ident, $operation: ident, $a: expr, $b: expr, $expected: expr) => {
            test_modes!($type, $operation, $a, $b, $expected, [
                ["public", "public", "private"],
                ["public", "constant", "private"],
                ["public", "private", "private"],
                ["private", "constant", "private"],
                ["private", "public", "private"],
                ["private", "private", "private"],
                ["constant", "private", "private"],
                ["constant", "public", "private"],
                ["constant", "constant", "constant"],
            ]);
        };

        ($type: ident, $operation: ident, $a: expr, $b: expr, $expected: expr, $modes: expr) => {
            paste::paste! {
                #[test]
                fn [<test_ $operation:lower _ $type _modes>]() {
                    use super::*;
                    use $crate::{
                        function::instructions::tests::test_binary,
                        Process,
                    };

                    for [a_mode, b_mode, expected_mode] in $modes.iter() {
                        test_binary::<$operation<Process>>(
                            &format!("{}.{}", $a, a_mode),
                            &format!("{}.{}", $b, b_mode),
                            &format!("{}.{}", $expected, expected_mode),
                        );
                    }
                }
            }
        };

        ($type: ident, $operation: ident, $input: expr, $expected: expr) => {
            paste::paste! {
                #[test]
                fn [<test_ $operation:lower _ $type _modes>]() {
                    use super::*;
                    use $crate::{
                        function::instructions::tests::test_unary,
                        Process,
                    };

                    test_unary::<$operation<Process>>(
                        &format!("{}.{}", $input, "public"),
                        &format!("{}.{}", $expected, "private"),
                    );

                    test_unary::<$operation<Process>>(
                        &format!("{}.{}", $input, "private"),
                        &format!("{}.{}", $expected, "private"),
                    );

                    test_unary::<$operation<Process>>(
                        &format!("{}.{}", $input, "constant"),
                        &format!("{}.{}", $expected, "constant"),
                    );
                }
            }
        };
    }
}
