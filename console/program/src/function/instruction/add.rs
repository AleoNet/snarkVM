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
        use core::ops::Add as Operator;

        // Perform the operation.
        let output = crate::evaluate!(match Operator::add(first, second) {
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

#[cfg(test)]
mod tests_rename {
    /// Creates a test of the given operation for each given case of inputs and outputs.
    ///
    /// ## Example
    /// ```ignore
    /// ```text
    ///     test_evaluate!(
    ///         Operator::add == AddOp::evaluate {
    ///             (Field, Field) => Field,
    ///             (Group, Group) => Group,
    ///             (I8, I8) => I8,
    ///             (I16, I16) => I16,
    ///             (I32, I32) => I32,
    ///             (I64, I64) => I64,
    ///             (I128, I128) => I128,
    ///             (U8, U8) => U8,
    ///             (U16, U16) => U16,
    ///             (U32, U32) => U32,
    ///             (U64, U64) => U64,
    ///             (U128, U128) => U128,
    ///             (Scalar, Scalar) => Scalar,
    ///         }
    ///     );
    /// ```
    #[macro_export]
    macro_rules! test_evaluate {
        // Case 1: Binary operation.
        ($operator:tt::$operation:ident == $opcode:tt::$op:ident { $( ($input_a:ident, $input_b:ident) => $output:ident $(($condition:tt))?, )+ }) => {
            // Invokes `Case 1A` or `Case 1B` (see below) for each given case of inputs and outputs.
            $( crate::test_evaluate!{$operator::$operation == $opcode::$op for ($input_a, $input_b) => $output $(($condition))?} )+
        };

        ////////////////////
        // Private Macros //
        ////////////////////

        // Case 1A: Binary operation.
        ($operator:tt::$operation:ident == $opcode:tt::$op:ident for ($input_a:ident, $input_b:ident) => $output:ident) => {
            paste::paste! {
                #[test]
                fn [<test _ $operation _ $input_a:lower _ $input_b:lower _ into _ $output:lower>]() -> Result<()> {
                    use snarkvm_console_types::*;

                    type CurrentNetwork = snarkvm_console_network::Testnet3;

                    // Ensure the expected output type is correct.
                    assert_eq!(LiteralType::$output, $opcode::<CurrentNetwork>::output_type((LiteralType::$input_a, LiteralType::$input_b))?);

                    // Check the operation on randomly-sampled values.
                    for _ in 0..1_000 {
                        // Sample the first and second value.
                        let a = $input_a::rand(&mut test_rng());
                        let b = $input_b::rand(&mut test_rng());

                        // Initialize the operands.
                        let first = Plaintext::from_str(&format!("{a}"))?;
                        let second = Plaintext::from_str(&format!("{b}"))?;

                        // Compute the outputs.
                        let expected = Plaintext::from(Literal::$output($operator::$operation(a, b)));
                        let candidate = $opcode::<CurrentNetwork>::$op((first, second))?;

                        // Ensure the outputs match.
                        assert_eq!(expected, candidate);
                    }

                    Ok(())
                }
            }
        };

        // Case 1B: Binary operation, where the sampled values are halved (divided by 2) to prevent overflows.
        ($operator:tt::$operation:ident == $opcode:tt::$op:ident for ($input_a:ident, $input_b:ident) => $output:ident ("skip overflows")) => {
            paste::paste! {
                #[test]
                fn [<test _ $operation _ $input_a:lower _ $input_b:lower _ into _ $output:lower>]() -> Result<()> {
                    use snarkvm_console_types::*;

                    type CurrentNetwork = snarkvm_console_network::Testnet3;

                    // Ensure the expected output type is correct.
                    assert_eq!(LiteralType::$output, $opcode::<CurrentNetwork>::output_type((LiteralType::$input_a, LiteralType::$input_b))?);

                    // Check the operation on randomly-sampled values.
                    for _ in 0..1_000 {
                        // Sample the first and second value.
                        let a = $input_a::rand(&mut test_rng()) / ($input_a::one() + $input_a::one());
                        let b = $input_b::rand(&mut test_rng()) / ($input_b::one() + $input_b::one());

                        // Initialize the operands.
                        let first = Plaintext::from_str(&format!("{a}"))?;
                        let second = Plaintext::from_str(&format!("{b}"))?;

                        // Compute the outputs.
                        let expected = Plaintext::from(Literal::$output($operator::$operation(a, b)));
                        let candidate = $opcode::<CurrentNetwork>::$op((first, second))?;

                        // Ensure the outputs match.
                        assert_eq!(expected, candidate);
                    }

                    Ok(())
                }
            }
        };

        // Case 1C: Binary operation, where the sampled values are invalid operands, and checked to halt.
        ($operator:tt::$operation:ident == $opcode:tt::$op:ident for ($input_a:ident, $input_b:ident) => $output:ident ("ensure invalid operands halt")) => {
            paste::paste! {
                #[test]
                fn [<test _ $operation _ $input_a:lower _ $input_b:lower _ into _ $output:lower _ halts _ on _ invalid _ operands>]() -> Result<()> {
                    use snarkvm_console_types::*;

                    type CurrentNetwork = snarkvm_console_network::Testnet3;

                    // Check the operation on randomly-sampled values.
                    for i in 0..1_000 {
                        // Sample the first and second value.
                        let a = $input_a::<CurrentNetwork>::rand(&mut test_rng());
                        let b = $input_b::<CurrentNetwork>::rand(&mut test_rng());

                        // Initialize the operands.
                        let first = Plaintext::from_str(&format!("{a}"))?;
                        let second = Plaintext::from_str(&format!("{b}"))?;

                        // Attempt to compute the overflow case.
                        let result = std::panic::catch_unwind(|| $opcode::<CurrentNetwork>::$op((first, second)));

                        // Ensure the computation halted.
                        assert!(result.is_err(), "An invalid operands case (on iteration {i}) did not halt: {a} {b}");
                    }

                    Ok(())
                }
            }
        };

        // Case 1D: Binary operation, where the sampled values are guaranteed to be overflow cases, and checked to halt.
        ($operator:tt::$operation:ident == $opcode:tt::$op:ident for ($input_a:ident, $input_b:ident) => $output:ident ("ensure overflows halt")) => {
            paste::paste! {
                #[test]
                fn [<test _ $operation _ $input_a:lower _ $input_b:lower _ into _ $output:lower _ halts _ on _ overflows>]() -> Result<()> {
                    use snarkvm_console_types::*;

                    type CurrentNetwork = snarkvm_console_network::Testnet3;

                    // Check the operation on randomly-sampled values.
                    for i in 0..1_000 {
                        // Sample the first and second value.
                        let a = $input_a::<CurrentNetwork>::rand(&mut test_rng());
                        let b = $input_b::<CurrentNetwork>::rand(&mut test_rng());

                        // Skip this iteration, if this is **not** an overflow case.
                        if (*a).[< checked _ $operation >](*b).is_some() {
                            // This case does not overflow, so skip it.
                            continue;
                        }

                        // Initialize the operands.
                        let first = Plaintext::from_str(&format!("{a}"))?;
                        let second = Plaintext::from_str(&format!("{b}"))?;

                        // Attempt to compute the overflow case.
                        let result = std::panic::catch_unwind(|| $opcode::<CurrentNetwork>::$op((first, second)));

                        // Ensure the computation halted.
                        assert!(result.is_err(), "Overflow case (on iteration {i}) did not halt: {a} {b}");
                    }

                    Ok(())
                }
            }
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Declare the operator to check.
    use core::ops::Add as Operator;

    // Declare the opcode to check.
    use super::AddOp as Opcode;

    // For each declared case, this macro samples random values and checks that
    // the output of the operator (LHS) matches the output of the opcode (RHS).
    crate::test_evaluate!(
        Operator::add == Opcode::evaluate {
            (Field, Field) => Field,
            (Group, Group) => Group,
            (I8, I8) => I8 ("skip overflows"),
            (I16, I16) => I16 ("skip overflows"),
            (I32, I32) => I32 ("skip overflows"),
            (I64, I64) => I64 ("skip overflows"),
            (I128, I128) => I128 ("skip overflows"),
            (U8, U8) => U8 ("skip overflows"),
            (U16, U16) => U16 ("skip overflows"),
            (U32, U32) => U32 ("skip overflows"),
            (U64, U64) => U64 ("skip overflows"),
            (U128, U128) => U128 ("skip overflows"),
            (Scalar, Scalar) => Scalar,
        }
    );

    // For each declared case, this macro samples random values and checks that
    // the output of the operator (LHS) matches the output of the opcode (RHS).
    crate::test_evaluate!(
        Operator::add == Opcode::evaluate {
            (I8, I8) => I8 ("ensure overflows halt"),
            (I16, I16) => I16 ("ensure overflows halt"),
            (I32, I32) => I32 ("ensure overflows halt"),
            (I64, I64) => I64 ("ensure overflows halt"),
            (I128, I128) => I128 ("ensure overflows halt"),
            (U8, U8) => U8 ("ensure overflows halt"),
            (U16, U16) => U16 ("ensure overflows halt"),
            (U32, U32) => U32 ("ensure overflows halt"),
            (U64, U64) => U64 ("ensure overflows halt"),
            (U128, U128) => U128 ("ensure overflows halt"),
        }
    );

    // // For each declared case, this macro samples random values and checks that
    // // the output of the operator (LHS) matches the output of the opcode (RHS).
    // // Ensure invalid operands halt.
    // crate::test_evaluate!(
    //     Opcode::evaluate {
    //         (Field, Field) => Field,
    //         (Group, Group) => Group,
    //         (I8, I8) => I8,
    //         (I16, I16) => I16,
    //         (I32, I32) => I32,
    //         (I64, I64) => I64,
    //         (I128, I128) => I128,
    //         (U8, U8) => U8,
    //         (U16, U16) => U16,
    //         (U32, U32) => U32,
    //         (U64, U64) => U64,
    //         (U128, U128) => U128,
    //         (Scalar, Scalar) => Scalar,
    //     }
    // );
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
