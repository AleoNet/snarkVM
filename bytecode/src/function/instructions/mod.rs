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

pub(super) mod prf;
pub(super) use prf::*;

pub(super) mod shl;
pub(super) use shl::*;

pub(super) mod shl_wrapped;
pub(super) use shl_wrapped::*;

pub(super) mod shr;
pub(super) use shr::*;

pub(super) mod shr_wrapped;
pub(super) use shr_wrapped::*;

pub(super) mod square;
pub(super) use square::*;

pub(super) mod sub;
pub(super) use sub::*;

pub(super) mod sub_wrapped;
pub(super) use sub_wrapped::*;

pub(super) mod ternary;
pub(super) use ternary::*;

pub(super) mod xor;
pub(super) use xor::*;

use crate::{
    function::{parsers::Operand, registers::Registers, Register},
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
    /// Performs a BHP commitment taking a 256-bit value as input.
    CommitBHP256(CommitBHP256<P>),
    /// Performs a BHP commitment taking a 512-bit value as input.
    CommitBHP512(CommitBHP512<P>),
    /// Performs a BHP commitment taking a 1024-bit value as input.
    CommitBHP1024(CommitBHP1024<P>),
    /// Performs a Pedersen commitment taking a 64-bit value as input.
    CommitPed64(CommitPed64<P>),
    /// Performs a Pedersen commitment taking a 128-bit value as input.
    CommitPed128(CommitPed128<P>),
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
    /// Performs a BHP hash taking a 256-bit value as input.
    HashBHP256(HashBHP256<P>),
    /// Performs a BHP hash taking a 512-bit value as input.
    HashBHP512(HashBHP512<P>),
    /// Performs a BHP hash taking a 1024-bit value as input.
    HashBHP1024(HashBHP1024<P>),
    /// Performs a Pedersen hash taking a 64-bit value as input.
    HashPed64(HashPed64<P>),
    /// Performs a Pedersen hash taking a 128-bit value as input.
    HashPed128(HashPed128<P>),
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
    /// Performs a Poseidon PRF with an input rate of 2.
    PRFPsd2(PRFPsd2<P>),
    /// Performs a Poseidon PRF with an input rate of 4.
    PRFPsd4(PRFPsd4<P>),
    /// Performs a Poseidon PRF with an input rate of 8.
    PRFPsd8(PRFPsd8<P>),
    /// Shifts `first` left by `second` bits, storing the outcome in `destination`.
    Shl(Shl<P>),
    /// Shifts `first` left by `second` bits, wrapping around at the boundary of the type, storing the outcome in `destination`.
    ShlWrapped(ShlWrapped<P>),
    /// Shifts `first` right by `second` bits, storing the outcome in `destination`.
    Shr(Shr<P>),
    /// Shifts `first` right by `second` bits, wrapping around at the boundary of the type, storing the outcome in `destination`.
    ShrWrapped(ShrWrapped<P>),
    /// Squares 'first', storing the outcome in `destination`.
    Square(Square<P>),
    /// Computes `first - second`, storing the outcome in `destination`.
    Sub(Sub<P>),
    /// Computes `first - second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    SubWrapped(SubWrapped<P>),
    /// Selects `first`, if `condition` is true, otherwise selects `second`, storing the result in `destination`.
    Ternary(Ternary<P>),
    /// Performs a bitwise Xor on `first` and `second`, storing the outcome in `destination`.
    Xor(Xor<P>),
}

/// Creates a match statement that applies the given operation for each instruction.
///
/// ## Example
/// ```ignore
/// instruction!(self, |instruction| write!(f, "{} {};", self.opcode(), instruction))
/// ```
/// The above example will print the opcode and the instruction to the given stream.
/// ```ignore
///     match self {
///         Self::Add(instruction) => write!(f, "{} {};", self.opcode(), instruction),
///         Self::Sub(instruction) => write!(f, "{} {};", self.opcode(), instruction),
///         Self::Mul(instruction) => write!(f, "{} {};", self.opcode(), instruction),
///         Self::Div(instruction) => write!(f, "{} {};", self.opcode(), instruction),
///     }
/// )
/// ```
#[macro_export]
macro_rules! instruction {
    // A variant **with** curly braces:
    // i.e. `instruction!(self, |instruction| { operation(instruction) })`.
    ($object:expr, |$input:ident| $operation:block) => {{
        instruction!(instruction, $object, |$input| $operation)
    }};
    // A variant **without** curly braces:
    // i.e. `instruction!(self, |instruction| operation(instruction))`.
    ($object:expr, |$input:ident| $operation:expr) => {{
        instruction!(instruction, $object, |$input| { $operation })
    }};
    // A variant **with** curly braces:
    // i.e. `instruction!(custom_macro, self, |instruction| { operation(instruction) })`.
    ($macro_:ident, $object:expr, |$input:ident| $operation:block) => {{
        $macro_!($object, |$input| $operation, {
            Abs,
            AbsWrapped,
            Add,
            AddWrapped,
            And,
            CommitBHP256,
            CommitBHP512,
            CommitBHP1024,
            CommitPed64,
            CommitPed128,
            Div,
            DivWrapped,
            Double,
            Equal,
            GreaterThan,
            GreaterThanOrEqual,
            HashBHP256,
            HashBHP512,
            HashBHP1024,
            HashPed64,
            HashPed128,
            HashPsd2,
            HashPsd4,
            HashPsd8,
            Inv,
            LessThan,
            LessThanOrEqual,
            Mul,
            MulWrapped,
            Nand,
            Neg,
            Nor,
            Not,
            NotEqual,
            Or,
            Pow,
            PowWrapped,
            PRFPsd2,
            PRFPsd4,
            PRFPsd8,
            Shl,
            ShlWrapped,
            Shr,
            ShrWrapped,
            Square,
            Sub,
            SubWrapped,
            Ternary,
            Xor,
        })
    }};
    // A variant **without** curly braces:
    // i.e. `instruction!(custom_macro, self, |instruction| operation(instruction))`.
    ($macro_:ident, $object:expr, |$input:ident| $operation:expr) => {{
        instruction!($macro_, $object, |$input| { $operation })
    }};
    // A variant invoking a macro internally:
    // i.e. `instruction!(instruction_to_bytes_le!(self, writer))`.
    ($macro_:ident!($object:expr, $input:ident)) => {{
        instruction!($macro_, $object, |$input| {})
    }};

    ////////////////////
    // Private Macros //
    ////////////////////

    // A static variant **with** curly braces:
    // i.e. `instruction!(self, |InstructionMember| { InstructionMember::opcode() })`.
    ($object:expr, |InstructionMember| $operation:block, { $( $variant:ident, )+ }) => {{
        // Build the match cases.
        match $object {
            $(
                Self::$variant(..) => {{
                    // Set the variant to be called `InstructionMember`.
                    type InstructionMember<P> = $variant<P>;
                    // Perform the operation.
                    $operation
                }}
            ),+
        }
    }};
    // A static variant **without** curly braces:
    // i.e. `instruction!(self, |InstructionMember| InstructionMember::opcode())`.
    ($object:expr, |InstructionMember| $operation:expr, { $( $variant:ident, )+ }) => {{
        instruction!($object, |InstructionMember| { $operation }, { $( $variant, )+ })
    }};
    // A non-static variant **with** curly braces:
    // i.e. `instruction!(self, |instruction| { operation(instruction) })`.
    ($object:expr, |$instruction:ident| $operation:block, { $( $variant:ident, )+ }) => {{
        // Build the match cases.
        match $object {
            $( Self::$variant($instruction) => { $operation } ),+
        }
    }};
    // A non-static variant **without** curly braces:
    // i.e. `instruction!(self, |instruction| operation(instruction))`.
    ($object:expr, |$instruction:ident| $operation:expr, { $( $variant:ident, )+ }) => {{
        instruction!($object, |$instruction| { $operation }, { $( $variant, )+ })
    }};
}

impl<P: Program> Instruction<P> {
    /// Returns the opcode of the instruction.
    #[inline]
    pub(crate) fn opcode(&self) -> &'static str {
        instruction!(self, |InstructionMember| InstructionMember::<P>::opcode())
    }

    /// Returns the operands of the instruction.
    #[inline]
    pub(crate) fn operands(&self) -> Vec<Operand<P>> {
        instruction!(self, |instruction| instruction.operands())
    }

    /// Returns the destination register of the instruction.
    #[inline]
    pub(crate) fn destination(&self) -> &Register<P> {
        instruction!(self, |instruction| instruction.destination())
    }

    /// Evaluates the instruction.
    #[inline]
    pub(crate) fn evaluate(&self, registers: &Registers<P>) {
        instruction!(self, |instruction| instruction.evaluate(registers))
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
                    preceded(pair(tag(CommitBHP256::<P>::opcode()), tag(" ")), map(CommitBHP256::parse, Into::into)),
                    preceded(pair(tag(CommitBHP512::<P>::opcode()), tag(" ")), map(CommitBHP512::parse, Into::into)),
                    preceded(pair(tag(CommitBHP1024::<P>::opcode()), tag(" ")), map(CommitBHP1024::parse, Into::into)),
                    preceded(pair(tag(CommitPed64::<P>::opcode()), tag(" ")), map(CommitPed64::parse, Into::into)),
                    preceded(pair(tag(CommitPed128::<P>::opcode()), tag(" ")), map(CommitPed128::parse, Into::into)),
                    preceded(pair(tag(Div::<P>::opcode()), tag(" ")), map(Div::parse, Into::into)),
                    preceded(pair(tag(DivWrapped::<P>::opcode()), tag(" ")), map(DivWrapped::parse, Into::into)),
                    preceded(pair(tag(Double::<P>::opcode()), tag(" ")), map(Double::parse, Into::into)),
                    preceded(pair(tag(Equal::<P>::opcode()), tag(" ")), map(Equal::parse, Into::into)),
                    preceded(pair(tag(GreaterThan::<P>::opcode()), tag(" ")), map(GreaterThan::parse, Into::into)),
                    preceded(
                        pair(tag(GreaterThanOrEqual::<P>::opcode()), tag(" ")),
                        map(GreaterThanOrEqual::parse, Into::into),
                    ),
                    preceded(pair(tag(HashBHP256::<P>::opcode()), tag(" ")), map(HashBHP256::parse, Into::into)),
                )),
                preceded(pair(tag(HashBHP512::<P>::opcode()), tag(" ")), map(HashBHP512::parse, Into::into)),
                preceded(pair(tag(HashBHP1024::<P>::opcode()), tag(" ")), map(HashBHP1024::parse, Into::into)),
                preceded(pair(tag(HashPed64::<P>::opcode()), tag(" ")), map(HashPed64::parse, Into::into)),
                preceded(pair(tag(HashPed128::<P>::opcode()), tag(" ")), map(HashPed128::parse, Into::into)),
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
            )),
            preceded(pair(tag(Or::<P>::opcode()), tag(" ")), map(Or::parse, Into::into)),
            preceded(pair(tag(Pow::<P>::opcode()), tag(" ")), map(Pow::parse, Into::into)),
            preceded(pair(tag(PowWrapped::<P>::opcode()), tag(" ")), map(PowWrapped::parse, Into::into)),
            preceded(pair(tag(PRFPsd2::<P>::opcode()), tag(" ")), map(PRFPsd2::parse, Into::into)),
            preceded(pair(tag(PRFPsd4::<P>::opcode()), tag(" ")), map(PRFPsd4::parse, Into::into)),
            preceded(pair(tag(PRFPsd8::<P>::opcode()), tag(" ")), map(PRFPsd8::parse, Into::into)),
            preceded(pair(tag(Shl::<P>::opcode()), tag(" ")), map(Shl::parse, Into::into)),
            preceded(pair(tag(ShlWrapped::<P>::opcode()), tag(" ")), map(ShlWrapped::parse, Into::into)),
            preceded(pair(tag(Shr::<P>::opcode()), tag(" ")), map(Shr::parse, Into::into)),
            preceded(pair(tag(ShrWrapped::<P>::opcode()), tag(" ")), map(ShrWrapped::parse, Into::into)),
            preceded(pair(tag(Square::<P>::opcode()), tag(" ")), map(Square::parse, Into::into)),
            preceded(pair(tag(Sub::<P>::opcode()), tag(" ")), map(Sub::parse, Into::into)),
            preceded(pair(tag(SubWrapped::<P>::opcode()), tag(" ")), map(SubWrapped::parse, Into::into)),
            preceded(pair(tag(Ternary::<P>::opcode()), tag(" ")), map(Ternary::parse, Into::into)),
            preceded(pair(tag(Xor::<P>::opcode()), tag(" ")), map(Xor::parse, Into::into)),
        ))(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, instruction))
    }
}

impl<P: Program> fmt::Display for Instruction<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        instruction!(self, |instruction| write!(f, "{} {};", self.opcode(), instruction))
    }
}

impl<P: Program> FromBytes for Instruction<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        /// Creates a match statement that produces the `FromBytes` implementation for the given instruction.
        ///
        /// ## Example
        /// ```ignore
        /// instruction_from_bytes_le!(self, |reader| {}, { Add, Sub, Mul, Div })
        /// ```
        macro_rules! instruction_from_bytes_le {
            ($object:expr, |$reader:ident| $_operation:block, { $( $variant:ident, )+ }) => {{
                // A list of instruction enum variants.
                const INSTRUCTION_VARIANTS: &[&'static str] = &[ $( stringify!($variant), )+];
                // Ensure the size is sufficiently large.
                assert!(INSTRUCTION_VARIANTS.len() <= u16::MAX as usize);

                // Read the enum variant index.
                let variant = u16::read_le(&mut $reader)?;

                // Build the cases for all instructions.
                $(
                    if INSTRUCTION_VARIANTS[variant as usize] == stringify!($variant) {
                        // Read the instruction.
                        let instruction = $variant::read_le(&mut $reader)?;
                        // Return the instruction.
                        return Ok(Self::$variant(instruction));
                    }
                )+
                // If the index is out of bounds, return an error.
                Err(error(format!("Failed to deserialize an instruction of variant {variant}")))
            }};
        }
        instruction!(instruction_from_bytes_le!(self, reader))
    }
}

impl<P: Program> ToBytes for Instruction<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        /// Creates a match statement that produces the `ToBytes` implementation for the given instruction.
        ///
        /// ## Example
        /// ```ignore
        /// instruction_to_bytes_le!(self, |writer| {}, { Add, Sub, Mul, Div })
        /// ```
        macro_rules! instruction_to_bytes_le {
            ($object:expr, |$writer:ident| $_operation:block, { $( $variant:ident, )+ }) => {{
                // A list of instruction enum variants.
                const INSTRUCTION_VARIANTS: &[&'static str] = &[ $( stringify!($variant), )+];
                // Ensure the size is sufficiently large.
                assert!(INSTRUCTION_VARIANTS.len() <= u16::MAX as usize);

                // Build the match cases.
                match $object {
                    $(
                        Self::$variant(instruction) => {
                            // Retrieve the enum variant index.
                            // Note: This unwrap is guaranteed to succeed because the enum variant is known to exist.
                            let variant = INSTRUCTION_VARIANTS.iter().position(|&name| stringify!($variant) == name).unwrap();

                            // Serialize the instruction.
                            u16::write_le(&(variant as u16),&mut $writer)?;
                            instruction.write_le(&mut $writer)?;
                        }
                    ),+
                }
                Ok(())
            }};
        }
        instruction!(instruction_to_bytes_le!(self, writer))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        function::{instructions::Opcode, Operation, Register, Registers},
        Parser,
        Process,
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
