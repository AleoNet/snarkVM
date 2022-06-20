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

mod opcode;
pub use opcode::*;

mod operand;
pub use operand::*;

mod operation;
pub use operation::*;

use crate::vm::{Program, Stack};
use console::{
    network::{
        prelude::{
            alt,
            bail,
            ensure,
            error,
            fmt,
            map,
            tag,
            Debug,
            Display,
            Error,
            Formatter,
            FromBytes,
            FromStr,
            IoResult,
            Parser,
            ParserResult,
            Read,
            Result,
            Sanitizer,
            ToBytes,
            Write,
        },
        Network,
    },
    program::{Register, RegisterType},
};

/// Creates a match statement that applies the given operation for each instruction.
///
/// ## Example
/// This example will print the opcode and the instruction to the given stream.
/// ```ignore
/// instruction!(self, |instruction| write!(f, "{} {};", self.opcode(), instruction))
/// ```
/// The above example is equivalent to the following logic:
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
    ($object:expr, |$input:ident| $operation:block) => {{ instruction!(instruction, $object, |$input| $operation) }};
    // A variant **without** curly braces:
    // i.e. `instruction!(self, |instruction| operation(instruction))`.
    ($object:expr, |$input:ident| $operation:expr) => {{ instruction!(instruction, $object, |$input| { $operation }) }};
    // A variant **with** curly braces:
    // i.e. `instruction!(custom_macro, self, |instruction| { operation(instruction) })`.
    ($macro_:ident, $object:expr, |$input:ident| $operation:block) => {
        $macro_!{$object, |$input| $operation, {
            Abs,
            AbsWrapped,
            Add,
            AddWrapped,
            And,
            Call,
            Cast,
            CommitBHP256,
            CommitBHP512,
            CommitBHP768,
            CommitBHP1024,
            // CommitPed64,
            // CommitPed128,
            // Div,
            // DivWrapped,
            Double,
            GreaterThan,
            GreaterThanOrEqual,
            HashBHP256,
            HashBHP512,
            HashBHP768,
            HashBHP1024,
            // HashPed64,
            // HashPed128,
            // HashPsd2,
            // HashPsd4,
            // HashPsd8,
            Inv,
            IsEqual,
            IsNotEqual,
            LessThan,
            LessThanOrEqual,
            Mul,
            MulWrapped,
            Nand,
            Neg,
            Nor,
            Not,
            Or,
            Pow,
            PowWrapped,
            Shl,
            ShlWrapped,
            Shr,
            ShrWrapped,
            Square,
            SquareRoot,
            Sub,
            SubWrapped,
            // Ternary,
            Xor,
        }}
    };
    // A variant **without** curly braces:
    // i.e. `instruction!(custom_macro, self, |instruction| operation(instruction))`.
    ($macro_:ident, $object:expr, |$input:ident| $operation:expr) => {{ instruction!($macro_, $object, |$input| { $operation }) }};
    // A variant invoking a macro internally:
    // i.e. `instruction!(instruction_to_bytes_le!(self, writer))`.
    ($macro_:ident!($object:expr, $input:ident)) => {{ instruction!($macro_, $object, |$input| {}) }};

    ////////////////////
    // Private Macros //
    ////////////////////

    // A static variant **with** curly braces:
    // i.e. `instruction!(self, |InstructionMember| { InstructionMember::opcode() })`.
    ($object:expr, |InstructionMember| $operation:block, { $( $variant:ident, )+ }) => {{
        // Build the match cases.
        match $object {
            $( Self::$variant(..) => {{
                // Set the variant to be called `InstructionMember`.
                type InstructionMember<N, A> = $variant<N, A>;
                // Perform the operation.
                $operation
            }} ),+
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
        match $object { $( Self::$variant($instruction) => { $operation } ),+ }
    }};
    // A non-static variant **without** curly braces:
    // i.e. `instruction!(self, |instruction| operation(instruction))`.
    ($object:expr, |$instruction:ident| $operation:expr, { $( $variant:ident, )+ }) => {{
        instruction!($object, |$instruction| { $operation }, { $( $variant, )+ })
    }};
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Instruction<N: Network, A: circuit::Aleo<Network = N>> {
    /// Compute the absolute value of `first`, checking for overflow, and storing the outcome in `destination`.
    Abs(Abs<N, A>),
    /// Compute the absolute value of `first`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    AbsWrapped(AbsWrapped<N, A>),
    /// Adds `first` with `second`, storing the outcome in `destination`.
    Add(Add<N, A>),
    /// Adds `first` with `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    AddWrapped(AddWrapped<N, A>),
    /// Performs a bitwise `and` operation on `first` and `second`, storing the outcome in `destination`.
    And(And<N, A>),
    /// Calls a closure on the operands.
    Call(Call<N, A>),
    /// Casts the operands into the declared type.
    Cast(Cast<N, A>),
    /// Performs a BHP commitment on inputs of 256-bit chunks.
    CommitBHP256(CommitBHP256<N, A>),
    /// Performs a BHP commitment on inputs of 512-bit chunks.
    CommitBHP512(CommitBHP512<N, A>),
    /// Performs a BHP commitment on inputs of 768-bit chunks.
    CommitBHP768(CommitBHP768<N, A>),
    /// Performs a BHP commitment on inputs of 1024-bit chunks.
    CommitBHP1024(CommitBHP1024<N, A>),
    // /// Performs a Pedersen commitment on up to a 64-bit input.
    // CommitPed64(CommitPed64<N, A>),
    // /// Performs a Pedersen commitment on up to a 128-bit input.
    // CommitPed128(CommitPed128<N, A>),
    // /// Divides `first` by `second`, storing the outcome in `destination`.
    // Div(Div<N, A>),
    // /// Divides `first` by `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    // DivWrapped(DivWrapped<N, A>),
    /// Doubles `first`, storing the outcome in `destination`.
    Double(Double<N, A>),
    /// Computes whether `first` is greater than `second` as a boolean, storing the outcome in `destination`.
    GreaterThan(GreaterThan<N, A>),
    /// Computes whether `first` is greater than or equal to `second` as a boolean, storing the outcome in `destination`.
    GreaterThanOrEqual(GreaterThanOrEqual<N, A>),
    /// Performs a BHP hash on inputs of 256-bit chunks.
    HashBHP256(HashBHP256<N, A>),
    /// Performs a BHP hash on inputs of 512-bit chunks.
    HashBHP512(HashBHP512<N, A>),
    /// Performs a BHP hash on inputs of 768-bit chunks.
    HashBHP768(HashBHP768<N, A>),
    /// Performs a BHP hash on inputs of 1024-bit chunks.
    HashBHP1024(HashBHP1024<N, A>),
    // /// Performs a Pedersen hash on up to a 64-bit input.
    // HashPed64(HashPed64<N, A>),
    // /// Performs a Pedersen hash on up to a 128-bit input.
    // HashPed128(HashPed128<N, A>),
    // /// Performs a Poseidon hash with an input rate of 2.
    // HashPsd2(HashPsd2<N, A>),
    // /// Performs a Poseidon hash with an input rate of 4.
    // HashPsd4(HashPsd4<N, A>),
    // /// Performs a Poseidon hash with an input rate of 8.
    // HashPsd8(HashPsd8<N, A>),
    /// Computes the multiplicative inverse of `first`, storing the outcome in `destination`.
    Inv(Inv<N, A>),
    /// Computes whether `first` equals `second` as a boolean, storing the outcome in `destination`.
    IsEqual(IsEqual<N, A>),
    /// Computes whether `first` does **not** equals `second` as a boolean, storing the outcome in `destination`.
    IsNotEqual(IsNotEqual<N, A>),
    /// Computes whether `first` is less than `second` as a boolean, storing the outcome in `destination`.
    LessThan(LessThan<N, A>),
    /// Computes whether `first` is less than or equal to `second` as a boolean, storing the outcome in `destination`.
    LessThanOrEqual(LessThanOrEqual<N, A>),
    /// Multiplies `first` with `second`, storing the outcome in `destination`.
    Mul(Mul<N, A>),
    /// Multiplies `first` with `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    MulWrapped(MulWrapped<N, A>),
    /// Returns `false` if `first` and `second` are true, storing the outcome in `destination`.
    Nand(Nand<N, A>),
    /// Negates `first`, storing the outcome in `destination`.
    Neg(Neg<N, A>),
    /// Returns `true` if neither `first` nor `second` is `true`, storing the outcome in `destination`.
    Nor(Nor<N, A>),
    /// Flips each bit in the representation of `first`, storing the outcome in `destination`.
    Not(Not<N, A>),
    /// Performs a bitwise `or` on `first` and `second`, storing the outcome in `destination`.
    Or(Or<N, A>),
    /// Raises `first` to the power of `second`, storing the outcome in `destination`.
    Pow(Pow<N, A>),
    /// Raises `first` to the power of `second`, wrapping around at the boundary of the type, storing the outcome in `destination`.
    PowWrapped(PowWrapped<N, A>),
    /// Shifts `first` left by `second` bits, storing the outcome in `destination`.
    Shl(Shl<N, A>),
    /// Shifts `first` left by `second` bits, continuing past the boundary of the type, storing the outcome in `destination`.
    ShlWrapped(ShlWrapped<N, A>),
    /// Shifts `first` right by `second` bits, storing the outcome in `destination`.
    Shr(Shr<N, A>),
    /// Shifts `first` right by `second` bits, continuing past the boundary of the type, storing the outcome in `destination`.
    ShrWrapped(ShrWrapped<N, A>),
    /// Squares 'first', storing the outcome in `destination`.
    Square(Square<N, A>),
    /// Compute the square root of 'first', storing the outcome in `destination`.
    SquareRoot(SquareRoot<N, A>),
    /// Computes `first - second`, storing the outcome in `destination`.
    Sub(Sub<N, A>),
    /// Computes `first - second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
    SubWrapped(SubWrapped<N, A>),
    // /// Selects `first`, if `condition` is true, otherwise selects `second`, storing the result in `destination`.
    // Ternary(Ternary<N, A>),
    /// Performs a bitwise `xor` on `first` and `second`, storing the outcome in `destination`.
    Xor(Xor<N, A>),
}

/// Derives `From<Operation>` for the instruction.
///
/// ## Example
/// ```ignore
/// derive_from_operation!(Instruction, |None| {}, { Add, Sub, Mul, Div })
/// ```
macro_rules! derive_from_operation {
    ($_object:expr, |$_reader:ident| $_operation:block, { $( $variant:ident, )+ }) => {
        $(impl<N: Network, A: circuit::Aleo<Network = N>> From<$variant<N, A>> for Instruction<N, A> {
            #[inline]
            fn from(operation: $variant<N, A>) -> Self {
                Self::$variant(operation)
            }
        })+
    }
}
instruction!(derive_from_operation, Instruction, |None| {});

/// Returns a slice of all instruction opcodes.
///
/// ## Example
/// ```ignore
/// opcodes!(Instruction, |None| {}, { Add, Sub, Mul, Div })
/// ```
macro_rules! opcodes {
    ($_object:expr, |$_reader:ident| $_operation:block, { $( $variant:ident, )+ }) => { [$( $variant::<N, A>::opcode() ),+] }
}

impl<N: Network, A: circuit::Aleo<Network = N>> Instruction<N, A> {
    /// The list of all instruction opcodes.
    pub const OPCODES: &'static [Opcode] = &instruction!(opcodes, Instruction, |None| {});
}

impl<N: Network, A: circuit::Aleo<Network = N>> Instruction<N, A> {
    /// Returns the opcode of the instruction.
    #[inline]
    pub const fn opcode(&self) -> Opcode {
        instruction!(self, |InstructionMember| InstructionMember::<N, A>::opcode())
    }

    /// Returns the operands of the instruction.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        instruction!(self, |instruction| instruction.operands())
    }

    /// Returns the destination register of the instruction.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        instruction!(self, |instruction| instruction.destinations())
    }

    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(&self, stack: &mut Stack<N, A>) -> Result<()> {
        instruction!(self, |instruction| instruction.evaluate(stack))
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute(&self, stack: &mut Stack<N, A>) -> Result<()> {
        instruction!(self, |instruction| instruction.execute(stack))
    }

    /// Returns the output type from the given input types.
    #[inline]
    pub fn output_types(
        &self,
        program: &Program<N, A>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        instruction!(self, |instruction| instruction.output_types(program, input_types))
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> Parser for Instruction<N, A> {
    /// Parses a string into an instruction.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Create an alt parser that matches the instruction.
        ///
        /// `nom` documentation notes that alt supports a maximum of 21 parsers.
        /// The documentation suggests to nest alt to support more parsers, as we do here.
        /// Note that order of the individual parsers matters.
        macro_rules! alt_parser {
            ($v0:expr) => {{ alt(($v0,)) }};
            ($v0:expr, $v1:expr) => {{ alt(($v0, $v1,)) }};
            ($v0:expr, $v1:expr, $v2:expr) => {{ alt(($v0, $v1, $v2,)) }};
            ($v0:expr, $v1:expr, $v2:expr, $v3:expr) => {{ alt(($v0, $v1, $v2, $v3,)) }};
            ($v0:expr, $v1:expr, $v2:expr, $v3:expr, $v4:expr) => {{ alt(($v0, $v1, $v2, $v3, $v4,)) }};
            ($v0:expr, $v1:expr, $v2:expr, $v3:expr, $v4:expr, $v5:expr) => {{ alt(($v0, $v1, $v2, $v3, $v4, $v5,)) }};
            ($v0:expr, $v1:expr, $v2:expr, $v3:expr, $v4:expr, $v5:expr, $v6:expr) => {{ alt(($v0, $v1, $v2, $v3, $v4, $v5, $v6,)) }};
            ($v0:expr, $v1:expr, $v2:expr, $v3:expr, $v4:expr, $v5:expr, $v6:expr, $v7:expr) => {{ alt(($v0, $v1, $v2, $v3, $v4, $v5, $v6, $v7,)) }};
            ($v0:expr, $v1:expr, $v2:expr, $v3:expr, $v4:expr, $v5:expr, $v6:expr, $v7:expr, $v8:expr) => {{ alt(($v0, $v1, $v2, $v3, $v4, $v5, $v6, $v7, $v8,)) }};
            ($v0:expr, $v1:expr, $v2:expr, $v3:expr, $v4:expr, $v5:expr, $v6:expr, $v7:expr, $v8:expr, $v9:expr) => {{ alt(($v0, $v1, $v2, $v3, $v4, $v5, $v6, $v7, $v8, $v9,)) }};
            ($v0:expr, $v1:expr, $v2:expr, $v3:expr, $v4:expr, $v5:expr, $v6:expr, $v7:expr, $v8:expr, $v9:expr, $( $variants:expr ),*) => {{ alt((
                alt_parser!($( $variants ),*), $v0, $v1, $v2, $v3, $v4, $v5, $v6, $v7, $v8, $v9,
            )) }};
        }

        /// Creates a parser for the given instructions.
        ///
        /// ## Example
        /// ```ignore
        /// instruction_parsers!(self, |_instruction| {}, { Add, Sub, Mul, Div })
        /// ```
        macro_rules! instruction_parsers {
            ($object:expr, |_instruction| $_operation:block, { $( $variant:ident, )+ }) => {{
                alt_parser!( $( map($variant::parse, Into::into) ),+ )
            }};
        }

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the instruction from the string.
        let (string, instruction) = instruction!(instruction_parsers!(self, _instruction))(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;

        Ok((string, instruction))
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> FromStr for Instruction<N, A> {
    type Err = Error;

    /// Parses a string into an instruction.
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

impl<N: Network, A: circuit::Aleo<Network = N>> Debug for Instruction<N, A> {
    /// Prints the instruction as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> Display for Instruction<N, A> {
    /// Prints the instruction as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        instruction!(self, |instruction| write!(f, "{};", instruction))
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> FromBytes for Instruction<N, A> {
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
                const INSTRUCTION_ENUMS: &[&'static str] = &[ $( stringify!($variant), )+];
                // Ensure the size is sufficiently large.
                assert!(INSTRUCTION_ENUMS.len() <= u16::MAX as usize);

                // Read the enum variant index.
                let variant = u16::read_le(&mut $reader)?;

                // Build the cases for all instructions.
                $(if INSTRUCTION_ENUMS[variant as usize] == stringify!($variant) {
                    // Read the instruction.
                    let instruction = $variant::read_le(&mut $reader)?;
                    // Return the instruction.
                    return Ok(Self::$variant(instruction));
                })+
                // If the index is out of bounds, return an error.
                Err(error(format!("Failed to deserialize an instruction of variant {variant}")))
            }};
        }
        instruction!(instruction_from_bytes_le!(self, reader))
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> ToBytes for Instruction<N, A> {
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
                const INSTRUCTION_ENUMS: &[&'static str] = &[ $( stringify!($variant), )+];
                // Ensure the size is sufficiently large.
                assert!(INSTRUCTION_ENUMS.len() <= u16::MAX as usize);

                // Build the match cases.
                match $object {
                    $(Self::$variant(instruction) => {
                        // Retrieve the enum variant index.
                        // Note: This unwrap is guaranteed to succeed because the enum variant is known to exist.
                        let variant = INSTRUCTION_ENUMS.iter().position(|&name| stringify!($variant) == name).unwrap();

                        // Serialize the instruction.
                        u16::write_le(&(variant as u16),&mut $writer)?;
                        instruction.write_le(&mut $writer)?;
                    }),+
                }
                Ok(())
            }};
        }
        instruction!(instruction_to_bytes_le!(self, writer))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit::network::AleoV0;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    #[test]
    fn test_opcodes() {
        // Sanity check the number of instructions is unchanged.
        assert_eq!(
            41,
            Instruction::<CurrentNetwork, CurrentAleo>::OPCODES.len(),
            "Update me if the number of instructions changes."
        );
    }
}
