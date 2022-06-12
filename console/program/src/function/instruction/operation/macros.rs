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

/// Creates a new `struct` that implements the `Operation` trait.
///
/// # Examples
/// ```ignore
/// operation!(
///     pub struct AddOperation<AddOperator, "add"> {
///         (Field, Field) => Field,
///         (Group, Group) => Group,
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
///         (Scalar, Scalar) => Scalar,
///     }
/// );
/// ```
#[macro_export]
macro_rules! operation {
    ($vis:vis struct $name:ident<$operator:path, $operation:ident, $opcode:tt> { $( ($input_a:ident, $input_b:ident) => $output:ident $(($condition:tt))?, )+ }) => {
        /// The implementation of the binary operation.
        $vis struct $name<N: Network>(core::marker::PhantomData<N>);

        impl<N: Network> $crate::function::instruction::Operation<N, $crate::Literal<N>, $crate::LiteralType, 2> for $name<N> {
            /// The opcode of the operation.
            const OPCODE: &'static str = $opcode;

            /// Returns the result of evaluating the operation on the given inputs.
            #[inline]
            fn evaluate(inputs: &[$crate::Literal<N>; 2]) -> Result<$crate::Literal<N>> {
                // Prepare the operator.
                use $operator as Operator;
                // Compute the output.
                Ok($crate::evaluate!(match Operator::$operation(inputs) { $( ($input_a, $input_b) => $output, )+ }))
            }

            /// Returns the output type from the given input types.
            #[inline]
            fn output_type(inputs: &[$crate::LiteralType; 2]) -> Result<$crate::LiteralType> {
                // Compute the output type.
                Ok($crate::output_type!(match inputs { $( ($input_a, $input_b) => $output, )+ }))
            }
        }

        paste::paste! {
            #[cfg(test)]
            mod [<test _ $operation>] {
                use super::$name;
                use snarkvm_console_network::prelude::*;
                // Prepare the operator.
                use $operator as Operator;
                // Create the test cases for the operation.
                $crate::test_evaluate!(Operator::$operation == $name::evaluate { $( ($input_a, $input_b) => $output $(($condition))?, )+ });
            }
        }
    };
}

/// Creates a match statement that evaluates the operation.
///
/// ## Example
/// ```ignore
/// evaluate!(
///     match Operator::add(inputs) {
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
macro_rules! evaluate {
    // Binary operation.
    (match $operator:tt::$operation:tt($inputs:expr) { $( ($input_a:ident, $input_b:ident) => $output:ident, )+ }) => {{
        // Retrieve the first and second operands.
        let [first, second] = $inputs;
        // Compute the output.
        match (first, second) {
            $(($crate::Literal::$input_a(first), $crate::Literal::$input_b(second)) => $crate::Literal::$output(first.$operation(second)),)+
            _ => bail!("Invalid operands for the '{}' instruction", Self::OPCODE),
        }
    }};
}

/// Creates a match statement that returns the output type given the input types.
///
/// ## Example
/// ```ignore
/// output_type!(
///     match (first, second) {
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
macro_rules! output_type {
    // Binary operation.
    (match $inputs:ident { $( ($input_a:ident, $input_b:ident) => $output:ident, )+ }) => {{
        // Retrieve the first and second operands.
        let [first, second] = $inputs;
        // Compute the output type.
        match (first, second) {
            $(($crate::LiteralType::$input_a, $crate::LiteralType::$input_b) => $crate::LiteralType::$output,)+
            _ => bail!("Invalid operand types for the '{}' instruction", Self::OPCODE),
        }
    }};
}

#[cfg(test)]
mod tests {
    /// Samples a random value for each literal type.
    #[macro_export]
    macro_rules! sample_literals {
        ($network:ident, $rng:expr) => {
            [
                $crate::Literal::<$network>::Address(Address::new(Uniform::rand($rng))),
                $crate::Literal::Boolean(Boolean::rand($rng)),
                $crate::Literal::Field(Field::rand($rng)),
                $crate::Literal::Group(Group::rand($rng)),
                $crate::Literal::I8(I8::rand($rng)),
                $crate::Literal::I16(I16::rand($rng)),
                $crate::Literal::I32(I32::rand($rng)),
                $crate::Literal::I64(I64::rand($rng)),
                $crate::Literal::I128(I128::rand($rng)),
                $crate::Literal::U8(U8::rand($rng)),
                $crate::Literal::U16(U16::rand($rng)),
                $crate::Literal::U32(U32::rand($rng)),
                $crate::Literal::U64(U64::rand($rng)),
                $crate::Literal::U128(U128::rand($rng)),
                $crate::Literal::Scalar(Scalar::rand($rng)),
                $crate::Literal::String(StringType::new(
                    &(0..<$network as Environment>::MAX_STRING_BYTES / 8)
                        .map(|_| $rng.gen::<char>())
                        .collect::<String>(),
                )),
            ]
        };
    }

    ///
    /// Creates a test of the given operation for each declared case.
    ///
    /// For each declared case, this macro samples random values and checks that
    /// the output of the operator (LHS) matches the output of the opcode (RHS).
    /// In addition, this macro ensures all combinations of literal types that
    /// do **not** match these declared cases fail on evaluation.
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
        ($operator:tt::$operation:tt == $opcode:tt::evaluate { $( ($input_a:ident, $input_b:ident) => $output:ident $(($condition:tt))?, )+ }) => {
            // For each given case of inputs and outputs, invoke `Case 1A` or `Case 1B` (see below).
            $( $crate::test_evaluate!{$operator::$operation == $opcode::evaluate for ($input_a, $input_b) => $output $(($condition))?} )+

            // For each non-existent case of inputs and outputs, invoke `Case 1C`.
            paste::paste! {
                #[test]
                fn [<test _ $operation _ fails _ on _ invalid _ operands>]() -> Result<()> {
                    use snarkvm_console_types::*;

                    type CurrentNetwork = snarkvm_console_network::Testnet3;

                    for i in 0..100 {
                        for literal_a in $crate::sample_literals!(CurrentNetwork, &mut test_rng()).iter() {
                            for literal_b in $crate::sample_literals!(CurrentNetwork, &mut test_rng()).iter() {
                                // Retrieve the types of the literals.
                                let (type_a, type_b) = (literal_a.to_type(), literal_b.to_type());

                                // Skip this iteration, if this is **not** an invalid operand case.
                                $(if type_a == $crate::LiteralType::$input_a && type_b == $crate::LiteralType::$input_b {
                                    continue;
                                })+

                                // Initialize the operands.
                                let first = $crate::Literal::from_str(&format!("{literal_a}"))?;
                                let second = $crate::Literal::from_str(&format!("{literal_b}"))?;

                                // Attempt to compute the invalid operand case.
                                let result = <$opcode::<CurrentNetwork> as $crate::function::instruction::Operation<_, _, _, 2>>::evaluate(&[first, second]);

                                // Ensure the computation failed.
                                assert!(result.is_err(), "An invalid operands case (on iteration {i}) did not fail: {literal_a} {literal_b}");
                            }
                        }
                    }
                    Ok(())
                }
            }
        };

        ////////////////////
        // Private Macros //
        ////////////////////

        // Case 1A: Binary operation.
        ($operator:tt::$operation:tt == $opcode:tt::evaluate for ($input_a:ident, $input_b:ident) => $output:ident) => {
            paste::paste! {
                #[test]
                fn [<test _ $operation _ $input_a:lower _ $input_b:lower _ into _ $output:lower>]() -> Result<()> {
                    use snarkvm_console_types::*;

                    type CurrentNetwork = snarkvm_console_network::Testnet3;

                    // Ensure the expected output type is correct.
                    assert_eq!(
                        $crate::LiteralType::from($crate::LiteralType::$output),
                        <$opcode::<CurrentNetwork> as $crate::function::instruction::Operation<_, _, _, 2>>::output_type(&[$crate::LiteralType::$input_a.into(), $crate::LiteralType::$input_b.into()])?
                    );

                    // Check the operation on randomly-sampled values.
                    for _ in 0..1_000 {
                        // Sample the first and second value.
                        let a = $input_a::<CurrentNetwork>::rand(&mut test_rng());
                        let b = $input_b::<CurrentNetwork>::rand(&mut test_rng());

                        // Initialize the operands.
                        let first = $crate::Literal::from_str(&format!("{a}"))?;
                        let second = $crate::Literal::from_str(&format!("{b}"))?;

                        // Compute the outputs.
                        let expected = $crate::Literal::$output(a.$operation(&b));
                        let candidate = <$opcode::<CurrentNetwork> as $crate::function::instruction::Operation<_, _, _, 2>>::evaluate(&[first, second])?;

                        // Ensure the outputs match.
                        assert_eq!(expected, candidate);
                    }

                    Ok(())
                }
            }
        };

        // Case 1B: Binary operation, where:
        //   1. If the sampled values overflow on evaluation, ensure it halts.
        //   2. If the sampled values **do not** overflow on evaluation, ensure it succeeds.
        ($operator:tt::$operation:tt == $opcode:tt::evaluate for ($input_a:ident, $input_b:ident) => $output:ident ("ensure overflows halt")) => {
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

                        // Initialize the operands.
                        let first = $crate::Literal::from_str(&format!("{a}"))?;
                        let second = $crate::Literal::from_str(&format!("{b}"))?;

                        // Skip this iteration, if this is **not** an overflow case.
                        match (*a).[< checked _ $operation >](*b).is_some() {
                            // If the sampled values **do not** overflow on evaluation, ensure it succeeds.
                            true => {
                                // Compute the outputs.
                                let expected = $crate::Literal::from($crate::Literal::$output(a.$operation(&b)));
                                let candidate = <$opcode::<CurrentNetwork> as $crate::function::instruction::Operation<_, _, _, 2>>::evaluate(&[first, second])?;
                                // Ensure the outputs match.
                                assert_eq!(expected, candidate);
                            },
                            // If the sampled values overflow on evaluation, ensure it halts.
                            false => {
                                // Attempt to compute the overflow case.
                                let result = std::panic::catch_unwind(|| <$opcode::<CurrentNetwork> as $crate::function::instruction::Operation<_, _, _, 2>>::evaluate(&[first, second]));
                                // Ensure the computation halted.
                                assert!(result.is_err(), "Overflow case (on iteration {i}) did not halt: {a} {b}");
                            }
                        }
                    }

                    Ok(())
                }
            }
        };

        // Case 1C: Binary operation, where:
        //   1. If the sampled divisor is zero, ensure it halts.
        //   2. If the sampled divisor is **not** zero, ensure it succeeds.
        ($operator:tt::$operation:tt == $opcode:tt::evaluate for ($input_a:ident, $input_b:ident) => $output:ident ("ensure divide by zero halts")) => {
            paste::paste! {
                #[test]
                fn [<test _ $operation _ $input_a:lower _ $input_b:lower _ into _ $output:lower _ halts _ on _ divide _ by _ zero>]() -> Result<()> {
                    use snarkvm_console_types::*;

                    type CurrentNetwork = snarkvm_console_network::Testnet3;

                    // Check the operation on randomly-sampled values.
                    for i in 0..1_000 {
                        // Sample the first and second value.
                        let a = $input_a::<CurrentNetwork>::rand(&mut test_rng());
                        let b = $input_b::<CurrentNetwork>::rand(&mut test_rng());

                        // Initialize the operands.
                        let first = $crate::Literal::from_str(&format!("{a}"))?;
                        let second = $crate::Literal::from_str(&format!("{b}"))?;

                        // Skip this iteration, if this is **not** an overflow case.
                        match (*a).checked_div(*b).is_some() {
                            // If the sampled values **do not** overflow on evaluation, ensure it succeeds.
                            true => {
                                // Compute the outputs.
                                let expected = $crate::Literal::from($crate::Literal::$output(a.$operation(&b)));
                                let candidate = <$opcode::<CurrentNetwork> as $crate::function::instruction::Operation<_, _, _, 2>>::evaluate(&[first, second])?;
                                // Ensure the outputs match.
                                assert_eq!(expected, candidate);
                            },
                            // If the sampled values overflow on evaluation, ensure it halts.
                            false => {
                                // Attempt to compute the overflow case.
                                let result = std::panic::catch_unwind(|| <$opcode::<CurrentNetwork> as $crate::function::instruction::Operation<_, _, _, 2>>::evaluate(&[first, second]));
                                // Ensure the computation halted.
                                assert!(result.is_err(), "Overflow case (on iteration {i}) did not halt: {a} {b}");
                            }
                        }
                    }

                    Ok(())
                }
            }
        };
    }
}
