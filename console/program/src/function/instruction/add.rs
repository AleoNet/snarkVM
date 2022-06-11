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
    function::instruction::{Binary, Operation},
    Literal,
    LiteralType,
    Plaintext,
};
use snarkvm_console_network::prelude::*;

use core::marker::PhantomData;

/// Adds `first` with `second`, storing the outcome in `destination`.
pub type Add<N> = Binary<N, AddOp<N>>;

pub struct AddOp<N: Network>(PhantomData<N>);

impl<N: Network> Operation for AddOp<N> {
    type InputTypes = (LiteralType, LiteralType);
    type Inputs = (Plaintext<N>, Plaintext<N>);
    type Output = Plaintext<N>;

    /// The opcode of the operation.
    const OPCODE: &'static str = "add";

    /// Returns the result of evaluating the operation on the given inputs.
    #[inline]
    fn evaluate((first, second): Self::Inputs) -> Result<Self::Output> {
        // Load the first literal.
        let first = match first {
            Plaintext::Literal(literal, ..) => literal,
            _ => bail!("Instruction '{}' expects a literal in the first operand.", Self::OPCODE),
        };

        // Load the second literal.
        let second = match second {
            Plaintext::Literal(literal, ..) => literal,
            _ => bail!("Instruction '{}' expects a literal in the second operand.", Self::OPCODE),
        };

        // Prepare the operator.
        use core::ops::Add as AddOperator;

        // Perform the operation.
        let output = crate::evaluate!(match AddOperator::add(first, second) {
            (Field, Field) => Field,
            (Group, Group) => Group,
            (I8, I8) => I8,
            (I16, I16) => I16,
            (I32, I32) => I32,
            (I64, I64) => I64,
            (I128, I128) => I128,
            (U8, U8) => U8,
            (U16, U16) => U16,
            (U32, U32) => U32,
            (U64, U64) => U64,
            (U128, U128) => U128,
            (Scalar, Scalar) => Scalar,
        });

        // Return the output.
        Ok(Plaintext::from(output))
    }

    /// Returns the output type from the given input types.
    #[inline]
    fn output_type((first, second): Self::InputTypes) -> Result<LiteralType> {
        // Compute the output type.
        Ok(crate::output_type!(match (first, second) {
            (Field, Field) => Field,
            (Group, Group) => Group,
            (I8, I8) => I8,
            (I16, I16) => I16,
            (I32, I32) => I32,
            (I64, I64) => I64,
            (I128, I128) => I128,
            (U8, U8) => U8,
            (U16, U16) => U16,
            (U32, U32) => U32,
            (U64, U64) => U64,
            (U128, U128) => U128,
            (Scalar, Scalar) => Scalar,
        }))
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::{function::Register, test_instruction_halts, test_modes, Identifier, Process, Value};
//
//     type P = Process;
//
//     #[test]
//     fn test_parse() {
//         let (_, instruction) = Instruction::<Process>::parse("add r0 r1 into r2;").unwrap();
//         assert!(matches!(instruction, Instruction::Add(_)));
//     }
//
//     test_modes!(field, Add, "1field", "2field", "3field");
//
//     mod group {
//         use super::*;
//         use crate::binary_instruction_test;
//
//         // 2group + 0group has special output mode behavior.
//         // Normally, a public variable plus a constant would yield a private variable. However, since
//         // the constant is zero, we return the original public variable.
//         binary_instruction_test!(
//             constant_and_constant_yields_constant,
//             Add,
//             "2group.constant",
//             "0group.constant",
//             "2group.constant"
//         );
//         binary_instruction_test!(
//             constant_and_public_yields_private,
//             Add,
//             "2group.constant",
//             "0group.public",
//             "2group.private"
//         );
//         binary_instruction_test!(
//             constant_and_private_yields_private,
//             Add,
//             "2group.constant",
//             "0group.private",
//             "2group.private"
//         );
//         binary_instruction_test!(
//             public_and_constant_yields_public,
//             Add,
//             "2group.public",
//             "0group.constant",
//             "2group.public"
//         );
//         binary_instruction_test!(
//             private_and_constant_yields_private,
//             Add,
//             "2group.private",
//             "0group.constant",
//             "2group.private"
//         );
//         binary_instruction_test!(
//             public_and_public_yields_private,
//             Add,
//             "2group.public",
//             "0group.public",
//             "2group.private"
//         );
//         binary_instruction_test!(
//             public_and_private_yields_private,
//             Add,
//             "2group.public",
//             "0group.private",
//             "2group.private"
//         );
//         binary_instruction_test!(
//             private_and_public_yields_private,
//             Add,
//             "2group.private",
//             "0group.public",
//             "2group.private"
//         );
//         binary_instruction_test!(
//             private_and_private_yields_private,
//             Add,
//             "2group.private",
//             "0group.private",
//             "2group.private"
//         );
//     }
//
//     test_modes!(i8, Add, "-1i8", "2i8", "1i8");
//     test_modes!(i16, Add, "-1i16", "2i16", "1i16");
//     test_modes!(i32, Add, "-1i32", "2i32", "1i32");
//     test_modes!(i64, Add, "-1i64", "2i64", "1i64");
//     test_modes!(i128, Add, "-1i128", "2i128", "1i128");
//     test_modes!(u8, Add, "1u8", "2u8", "3u8");
//     test_modes!(u16, Add, "1u16", "2u16", "3u16");
//     test_modes!(u32, Add, "1u32", "2u32", "3u32");
//     test_modes!(u64, Add, "1u64", "2u64", "3u64");
//     test_modes!(u128, Add, "1u128", "2u128", "3u128");
//     test_modes!(scalar, Add, "1scalar", "2scalar", "3scalar");
//
//     test_instruction_halts!(
//         i8_overflow_halts,
//         Add,
//         "Integer overflow on addition of two constants",
//         &format!("{}i8.constant", i8::MAX),
//         "1i8.constant"
//     );
//     test_instruction_halts!(
//         i16_overflow_halts,
//         Add,
//         "Integer overflow on addition of two constants",
//         &format!("{}i16.constant", i16::MAX),
//         "1i16.constant"
//     );
//     test_instruction_halts!(
//         i32_overflow_halts,
//         Add,
//         "Integer overflow on addition of two constants",
//         &format!("{}i32.constant", i32::MAX),
//         "1i32.constant"
//     );
//     test_instruction_halts!(
//         i64_overflow_halts,
//         Add,
//         "Integer overflow on addition of two constants",
//         &format!("{}i64.constant", i64::MAX),
//         "1i64.constant"
//     );
//     test_instruction_halts!(
//         i128_overflow_halts,
//         Add,
//         "Integer overflow on addition of two constants",
//         &format!("{}i128.constant", i128::MAX),
//         "1i128.constant"
//     );
//     test_instruction_halts!(
//         u8_overflow_halts,
//         Add,
//         "Integer overflow on addition of two constants",
//         &format!("{}u8.constant", u8::MAX),
//         "1u8.constant"
//     );
//     test_instruction_halts!(
//         u16_overflow_halts,
//         Add,
//         "Integer overflow on addition of two constants",
//         &format!("{}u16.constant", u16::MAX),
//         "1u16.constant"
//     );
//     test_instruction_halts!(
//         u32_overflow_halts,
//         Add,
//         "Integer overflow on addition of two constants",
//         &format!("{}u32.constant", u32::MAX),
//         "1u32.constant"
//     );
//     test_instruction_halts!(
//         u64_overflow_halts,
//         Add,
//         "Integer overflow on addition of two constants",
//         &format!("{}u64.constant", u64::MAX),
//         "1u64.constant"
//     );
//     test_instruction_halts!(
//         u128_overflow_halts,
//         Add,
//         "Integer overflow on addition of two constants",
//         &format!("{}u128.constant", u128::MAX),
//         "1u128.constant"
//     );
//
//     test_instruction_halts!(
//         address_halts,
//         Add,
//         "Invalid 'add' instruction",
//         "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant",
//         "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.constant"
//     );
//     test_instruction_halts!(boolean_halts, Add, "Invalid 'add' instruction", "true.constant", "true.constant");
//     test_instruction_halts!(string_halts, Add, "Invalid 'add' instruction", "\"hello\".constant", "\"world\".constant");
//
//     #[test]
//     #[should_panic(expected = "Operand is not a literal")]
//     fn test_definition_halts() {
//         let first = Value::<N>>::Definition(Identifier::from_str("message"), vec![
//             Value::from_str("2group.public"),
//             Value::from_str("10field.private"),
//         ]);
//         let second = first.clone();
//
//         let registers = Registers::<N>>::default();
//         registers.define(&Register::from_str("r0"));
//         registers.define(&Register::from_str("r1"));
//         registers.define(&Register::from_str("r2"));
//         registers.assign(&Register::from_str("r0"), first);
//         registers.assign(&Register::from_str("r1"), second);
//
//         Add::from_str("r0 r1 into r2").evaluate(&registers);
//     }
// }
