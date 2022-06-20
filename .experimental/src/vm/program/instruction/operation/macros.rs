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
    // Unary operation.
    ($vis:vis struct $name:ident<$operator:path, $circuit_operator:path, $operate:ident, $opcode:tt> { $( $input:ident => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
        $crate::operation!($vis struct $name<$operator, $circuit_operator, $operate, $opcode, 1> { $( ($input) => $output $( ( $($condition),+ ) )?, )+ });
    };
    // Unary operation with question mark (?).
    ($vis:vis struct $name:ident<$operator:path, $circuit_operator:path, $operate:ident?, $opcode:tt> { $( $input:ident => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
        $crate::operation!($vis struct $name<$operator, $circuit_operator, $operate?, $opcode, 1> { $( ($input) => $output $( ( $($condition),+ ) )?, )+ });
    };
    // Binary operation.
    ($vis:vis struct $name:ident<$operator:path, $circuit_operator:path, $operate:ident, $opcode:tt> { $( ($input_a:ident, $input_b:ident) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
        $crate::operation!($vis struct $name<$operator, $circuit_operator, $operate, $opcode, 2> { $( ($input_a, $input_b) => $output $( ( $($condition),+ ) )?, )+ });
    };
    // Ternary operation.
    ($vis:vis struct $name:ident<$operator:path, $circuit_operator:path, $operate:ident, $opcode:tt> { $( ($input_a:ident, $input_b:ident, $input_c:ident) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
        $crate::operation!($vis struct $name<$operator, $circuit_operator, $operate, $opcode, 3> { $( ($input_a, $input_b, $input_c) => $output $( ( $($condition),+ ) )?, )+ });
    };
    // K-ary operation.
    ($vis:vis struct $name:ident<$operator:path, $circuit_operator:path, $operate:ident, $opcode:tt, $num_inputs:tt> { $( ( $($input:ident),+ ) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
        /// The implementation of the binary operation.
        #[derive(Clone, PartialEq, Eq, Hash)]
        $vis struct $name<N: Network, A: circuit::Aleo>(core::marker::PhantomData<(N, A)>);

        impl<N: Network, A: circuit::Aleo> $crate::vm::Operation<N, console::program::Literal<N>, circuit::Literal<A>, console::program::LiteralType, $num_inputs> for $name<N, A> {
            /// The opcode of the operation.
            const OPCODE: $crate::vm::Opcode = Opcode::Literal($opcode);

            /// Returns the result of evaluating the operation on the given inputs.
            #[inline]
            fn evaluate(inputs: &[console::program::Literal<N>; $num_inputs]) -> Result<console::program::Literal<N>> {
                // Prepare the operator.
                use $operator as Operator;
                // Compute the output.
                Ok($crate::evaluate!(match Operator::$operate(inputs) { $( ( $($input),+ ) => $output, )+ }))
            }

            /// Returns the result of executing the operation on the given circuit inputs.
            #[inline]
            fn execute(inputs: &[circuit::Literal<A>; $num_inputs]) -> Result<circuit::Literal<A>> {
                // Prepare the circuit operator.
                use $circuit_operator as Operator;
                // Compute the output.
                Ok($crate::execute!(match Operator::$operate(inputs) { $( ( $($input),+ ) => $output, )+ }))
            }

            /// Returns the output type from the given input types.
            #[inline]
            fn output_type(inputs: &[console::program::LiteralType; $num_inputs]) -> Result<console::program::LiteralType> {
                // Compute the output type.
                Ok($crate::output_type!(match inputs { $( ( $($input),+ ) => $output, )+ }))
            }
        }

        paste::paste! {
            #[cfg(test)]
            mod [<test _ $operate>] {
                use super::$name;
                use console::{network::prelude::*, types::*};

                // Prepare the environment.
                type CurrentNetwork = console::network::Testnet3;
                type CurrentAleo = circuit::network::AleoV0;

                // Prepare the operator.
                use $operator as Operator;
                // Prepare the operation.
                type Operation = $name::<CurrentNetwork, CurrentAleo>;
                // Execute the test cases for the operation.
                $crate::test_execute!(Operator::$operate == Operation::execute { $( ( $($input),+ ) => $output $( ($($condition),+) )?, )+ });
            }
        }
    };
    // K-ary operation with question mark (?).
    ($vis:vis struct $name:ident<$operator:path, $circuit_operator:path, $operate:ident?, $opcode:tt, $num_inputs:tt> { $( ( $($input:ident),+ ) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
        /// The implementation of the binary operation.
        #[derive(Clone, PartialEq, Eq, Hash)]
        $vis struct $name<N: Network, A: circuit::Aleo>(core::marker::PhantomData<(N, A)>);

        impl<N: Network, A: circuit::Aleo> $crate::vm::Operation<N, console::program::Literal<N>, circuit::Literal<A>, console::program::LiteralType, $num_inputs> for $name<N, A> {
            /// The opcode of the operation.
            const OPCODE: $crate::vm::Opcode = Opcode::Literal($opcode);

            /// Returns the result of evaluating the operation on the given inputs.
            #[inline]
            fn evaluate(inputs: &[console::program::Literal<N>; $num_inputs]) -> Result<console::program::Literal<N>> {
                // Prepare the operator.
                use $operator as Operator;
                // Compute the output.
                Ok($crate::evaluate!(match Operator::$operate(inputs)? { $( ( $($input),+ ) => $output, )+ }))
            }

            /// Returns the result of executing the operation on the given circuit inputs.
            #[inline]
            fn execute(inputs: &[circuit::Literal<A>; $num_inputs]) -> Result<circuit::Literal<A>> {
                // Prepare the circuit operator.
                use $circuit_operator as Operator;
                // Compute the output.
                Ok($crate::execute!(match Operator::$operate(inputs) { $( ( $($input),+ ) => $output, )+ }))
            }

            /// Returns the output type from the given input types.
            #[inline]
            fn output_type(inputs: &[console::program::LiteralType; $num_inputs]) -> Result<console::program::LiteralType> {
                // Compute the output type.
                Ok($crate::output_type!(match inputs { $( ( $($input),+ ) => $output, )+ }))
            }
        }

        paste::paste! {
            #[cfg(test)]
            mod [<test _ $operate>] {
                use super::$name;
                use console::{network::prelude::*, types::*};

                // Prepare the environment.
                type CurrentNetwork = console::network::Testnet3;
                type CurrentAleo = circuit::network::AleoV0;

                // Prepare the operator.
                use $operator as Operator;
                // Prepare the operation.
                type Operation = $name::<CurrentNetwork, CurrentAleo>;
                // Execute the test cases for the operation.
                $crate::test_execute!(Operator::$operate == Operation::execute? { $( ( $($input),+ ) => $output $( ($($condition),+) )?, )+ });
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
    // Unary operation.
    (match $operator:tt::$operate:tt($inputs:expr) { $( ($input:ident) => $output:ident, )+ }) => {{
        // Retrieve the operand.
        let [first] = $inputs;
        // Compute the output.
        match first {
            $(console::program::Literal::$input(first) => console::program::Literal::$output(first.$operate()),)+
            _ => bail!("Invalid operand for the '{}' instruction", Self::OPCODE),
        }
    }};
    // Unary operation with question mark (?).
    (match $operator:tt::$operate:tt($inputs:expr)? { $( ( $input:ident ) => $output:ident, )+ }) => {{
        // Retrieve the operand.
        let [first] = $inputs;
        // Compute the output.
        match first {
            $(console::program::Literal::$input(first) => console::program::Literal::$output(first.$operate()?),)+
            _ => bail!("Invalid operand for the '{}' instruction", Self::OPCODE),
        }
    }};
    // Binary operation.
    (match $operator:tt::$operate:tt($inputs:expr) { $( ($input_a:ident, $input_b:ident) => $output:ident, )+ }) => {{
        // Retrieve the operands.
        let [first, second] = $inputs;
        // Compute the output.
        match (first, second) {
            $((console::program::Literal::$input_a(first), console::program::Literal::$input_b(second)) => console::program::Literal::$output(first.$operate(second)),)+
            _ => bail!("Invalid operands for the '{}' instruction", Self::OPCODE),
        }
    }};
    // Ternary operation.
    (match $operator:tt::$operate:tt($inputs:expr) { $( ($input_a:ident, $input_b:ident, $input_c:ident) => $output:ident, )+ }) => {{
        // Retrieve the operands.
        let [first, second, third] = $inputs;
        // Compute the output.
        match (first, second, third) {
            $((console::program::Literal::$input_a(first), console::program::Literal::$input_b(second), console::program::Literal::$input_c(third)) => console::program::Literal::$output(first.$operate(second, third)),)+
            _ => bail!("Invalid operands for the '{}' instruction", Self::OPCODE),
        }
    }};
}

/// Creates a match statement that executes the operation.
///
/// ## Example
/// ```ignore
/// execute!(
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
macro_rules! execute {
    // Unary operation.
    (match $operator:tt::$operate:tt($inputs:expr) { $( ($input:ident) => $output:ident, )+ }) => {{
        // Retrieve the operand.
        let [first] = $inputs.to_owned();
        // Compute the output.
        match first {
            $(circuit::Literal::$input(first) => circuit::Literal::$output(first.$operate()),)+
            _ => bail!("Invalid operand for the '{}' instruction", Self::OPCODE),
        }
    }};
    // Binary operation.
    (match $operator:tt::$operate:tt($inputs:expr) { $( ($input_a:ident, $input_b:ident) => $output:ident, )+ }) => {{
        // Retrieve the operands.
        let [first, second] = $inputs.to_owned();
        // Compute the output.
        match (first, second) {
            $((circuit::Literal::$input_a(first), circuit::Literal::$input_b(second)) => circuit::Literal::$output(first.$operate(&second)),)+
            _ => bail!("Invalid operands for the '{}' instruction", Self::OPCODE),
        }
    }};
    // Ternary operation.
    (match $operator:tt::$operate:tt($inputs:expr) { $( ($input_a:ident, $input_b:ident, $input_c:ident) => $output:ident, )+ }) => {{
        // Retrieve the operands.
        let [first, second] = $inputs.to_owned();
        // Compute the output.
        match (first, second, third) {
            $((circuit::Literal::$input_a(first), circuit::Literal::$input_b(second), circuit::Literal::$input_c(third)) => circuit::Literal::$output(first.$operate(&second, &third)),)+
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
    // Unary operation.
    (match $inputs:ident { $( ($input:ident) => $output:ident, )+ }) => {{
        // Retrieve the operand.
        let [first] = $inputs;
        // Compute the output type.
        match first {
            $(console::program::LiteralType::$input => console::program::LiteralType::$output,)+
            _ => bail!("Invalid operand types for the '{}' instruction", Self::OPCODE),
        }
    }};
    // Binary operation.
    (match $inputs:ident { $( ($input_a:ident, $input_b:ident) => $output:ident, )+ }) => {{
        // Retrieve the operands.
        let [first, second] = $inputs;
        // Compute the output type.
        match (first, second) {
            $((console::program::LiteralType::$input_a, console::program::LiteralType::$input_b) => console::program::LiteralType::$output,)+
            _ => bail!("Invalid operand types for the '{}' instruction", Self::OPCODE),
        }
    }};
    // Ternary operation.
    (match $inputs:ident { $( ($input_a:ident, $input_b:ident, $input_c:ident) => $output:ident, )+ }) => {{
        // Retrieve the operands.
        let [first, second, third] = $inputs;
        // Compute the output type.
        match (first, second, third) {
            $((console::program::LiteralType::$input_a, console::program::LiteralType::$input_b, console::program::LiteralType::$input_c) => console::program::LiteralType::$output,)+
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
                console::program::Literal::<$network>::Address(Address::new(Uniform::rand($rng))),
                console::program::Literal::Boolean(Boolean::rand($rng)),
                console::program::Literal::Field(Field::rand($rng)),
                console::program::Literal::Group(Group::rand($rng)),
                console::program::Literal::I8(I8::rand($rng)),
                console::program::Literal::I16(I16::rand($rng)),
                console::program::Literal::I32(I32::rand($rng)),
                console::program::Literal::I64(I64::rand($rng)),
                console::program::Literal::I128(I128::rand($rng)),
                console::program::Literal::U8(U8::rand($rng)),
                console::program::Literal::U16(U16::rand($rng)),
                console::program::Literal::U32(U32::rand($rng)),
                console::program::Literal::U64(U64::rand($rng)),
                console::program::Literal::U128(U128::rand($rng)),
                console::program::Literal::Scalar(Scalar::rand($rng)),
                console::program::Literal::String(StringType::new(
                    &$rng
                        .sample_iter(&Alphanumeric)
                        .take((<$network as Environment>::MAX_STRING_BYTES / 4) as usize)
                        .map(char::from)
                        .collect::<String>(),
                )),
            ]
        };
    }

    ///
    /// Creates a test of the given operation for each declared case.
    ///
    /// For each declared case, this macro samples random values and checks that
    /// the output of the operator (LHS) matches the output of the operation (RHS).
    /// In addition, this macro ensures all combinations of literal types that
    /// do **not** match these declared cases fail on evaluation.
    ///
    /// ## Example
    /// ```ignore
    /// ```text
    ///     test_execute!(
    ///         Operator::add == AddOp::execute {
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
    macro_rules! test_execute {
        // Case 0: Unary operation.
        ($operator:tt::$operate:tt == $operation:tt::$execute:tt { $( ($input:ident) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
            // For each given case of inputs and outputs, invoke `Case 0-A` or `Case 0-B` (see below).
            $( $crate::test_execute!{$operator::$operate == $operation::$execute for $input => $output $( ($($condition),+) )?} )+
            // For each non-existent case of inputs and outputs, invoke the following test to ensure the operation **fails**.
            paste::paste! {
                #[test]
                fn [<test _ $operate _ fails _ on _ invalid _ operands>]() -> Result<()> {
                    for i in 0..10 {
                        for literal_a in $crate::sample_literals!(CurrentNetwork, &mut test_rng()).iter() {
                            for mode_a in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                                // Skip this iteration, if this is **not** an invalid operand case.
                                $(if literal_a.to_type() == console::program::LiteralType::$input {
                                    continue;
                                })+

                                // Attempt to compute the invalid operand case.
                                let result_a = <$operation as $crate::vm::Operation<_, _, _, _, 1>>::evaluate(&[literal_a.clone()]);
                                // Ensure the computation failed.
                                assert!(result_a.is_err(), "An invalid operands case (on iteration {i}) did not fail (console): {literal_a}");

                                // Attempt to compute the invalid operand case.
                                let result_b = <$operation as $crate::vm::Operation<_, _, _, _, 1>>::$execute(&[
                                    circuit::program::Literal::from_str(&format!("{literal_a}.{mode_a}"))?,
                                ]);
                                // Ensure the computation failed.
                                assert!(result_b.is_err(), "An invalid operands case (on iteration {i}) did not fail (circuit): {literal_a}");
                                // Reset the circuit.
                                <CurrentAleo as circuit::Environment>::reset();
                            }
                        }
                    }
                    Ok(())
                }
            }
        };

        // Case 0Q: Unary operation with question mark (?).
        ($operator:tt::$operate:tt == $operation:tt::$execute:tt? { $( ($input:ident) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
            // For each given case of inputs and outputs, invoke `Case 0Q-A` or `Case 0Q-B` (see below).
            $( $crate::test_execute!{$operator::$operate == $operation::$execute (.unwrap()) for $input => $output $( ($($condition),+) )?} )+
            // For each non-existent case of inputs and outputs, invoke the following test to ensure the operation **fails**.
            paste::paste! {
                #[test]
                fn [<test _ $operate _ fails _ on _ invalid _ operands>]() -> Result<()> {
                    for i in 0..10 {
                        for literal_a in $crate::sample_literals!(CurrentNetwork, &mut test_rng()).iter() {
                            for mode_a in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                                // Skip this iteration, if this is **not** an invalid operand case.
                                $(if literal_a.to_type() == console::program::LiteralType::$input {
                                    continue;
                                })+

                                // Attempt to compute the invalid operand case.
                                let result_a = <$operation as $crate::vm::Operation<_, _, _, _, 1>>::evaluate(&[literal_a.clone()]);
                                // Ensure the computation failed.
                                assert!(result_a.is_err(), "An invalid operands case (on iteration {i}) did not fail (console): {literal_a}");

                                // Attempt to compute the invalid operand case.
                                let result_b = <$operation as $crate::vm::Operation<_, _, _, _, 1>>::$execute(&[
                                    circuit::program::Literal::from_str(&format!("{literal_a}.{mode_a}"))?,
                                ]);
                                // Ensure the computation failed.
                                assert!(result_b.is_err(), "An invalid operands case (on iteration {i}) did not fail (circuit): {literal_a}");
                                // Reset the circuit.
                                <CurrentAleo as circuit::Environment>::reset();
                            }
                        }
                    }
                    Ok(())
                }
            }
        };

        // Case 1: Binary operation.
        ($operator:tt::$operate:tt == $operation:tt::$execute:tt { $( ($input_a:ident, $input_b:ident) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
            // For each given case of inputs and outputs, invoke `Case 1-A` or `Case 1-B` (see below).
            $( $crate::test_execute!{$operator::$operate == $operation::$execute for ($input_a, $input_b) => $output $( ($($condition),+) )?} )+

            // For each non-existent case of inputs and outputs, invoke the following test to ensure the operation **fails**.
            paste::paste! {
                #[test]
                fn [<test _ $operate _ fails _ on _ invalid _ operands>]() -> Result<()> {
                    for i in 0..10 {
                        for literal_a in $crate::sample_literals!(CurrentNetwork, &mut test_rng()).iter() {
                            for literal_b in $crate::sample_literals!(CurrentNetwork, &mut test_rng()).iter() {
                                for mode_a in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                                    for mode_b in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                                        // Skip this iteration, if this is **not** an invalid operand case.
                                        $(if literal_a.to_type() == console::program::LiteralType::$input_a
                                          && literal_b.to_type() == console::program::LiteralType::$input_b {
                                            continue;
                                        })+

                                        // Attempt to compute the invalid operand case.
                                        let result_a = <$operation as $crate::vm::Operation<_, _, _, _, 2>>::evaluate(&[literal_a.clone(), literal_b.clone()]);
                                        // Ensure the computation failed.
                                        assert!(result_a.is_err(), "An invalid operands case (on iteration {i}) did not fail (console): {literal_a} {literal_b}");

                                        // Attempt to compute the invalid operand case.
                                        let result_b = <$operation as $crate::vm::Operation<_, _, _, _, 2>>::$execute(&[
                                            circuit::program::Literal::from_str(&format!("{literal_a}.{mode_a}"))?,
                                            circuit::program::Literal::from_str(&format!("{literal_b}.{mode_b}"))?,
                                        ]);
                                        // Ensure the computation failed.
                                        assert!(result_b.is_err(), "An invalid operands case (on iteration {i}) did not fail (circuit): {literal_a} {literal_b}");
                                        // Reset the circuit.
                                        <CurrentAleo as circuit::Environment>::reset();
                                    }
                                }
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

        // Case 0-A: Unary operation.
        // Case 0-B: Unary operation, where:
        //   1. "ensure overflow halts"
        //     - If the sampled values overflow on evaluation, ensure it halts.
        //     - If the sampled values **do not** overflow on evaluation, ensure it succeeds.
        ($operator:tt::$operate:tt == $operation:tt::$execute:tt $((.$unwrap:tt()))? for $input:ident => $output:ident $( ($($condition:tt),+) )?) => {
            paste::paste! {
                #[test]
                fn [<test _ $operate _ $input:lower _ into _ $output:lower>]() -> Result<()> {
                    // Ensure the expected output type is correct.
                    assert_eq!(
                        console::program::LiteralType::$output,
                        <$operation as $crate::vm::Operation<_, _, _, _, 1>>::output_type(&[console::program::LiteralType::$input.into()])?
                    );

                    // Check the operation on randomly-sampled values.
                    for i in 0..150u64 {
                        // Sample the first and second value.
                        #[allow(deprecated)]
                        let a = match i {
                            0 => $input::zero(),
                            1.. => $input::<CurrentNetwork>::rand(&mut test_rng())
                        };

                        // Initialize an indicator whether the operation should succeed or not.
                        #[allow(unused_mut)]
                        let mut should_succeed = true;
                        /// A helper macro to check the conditions.
                        macro_rules! check_condition {
                            ("ensure overflows halt") => {
                                match *<$operation as $crate::vm::Operation<_, _, _, _, 1>>::OPCODE {
                                    "abs" | "abs.w" => should_succeed &= (*a).checked_abs().is_some(),
                                    "neg" | "neg.w" => should_succeed &= (*a).checked_neg().is_some(),
                                    _ => panic!("Unsupported test enforcement for '{}'", <$operation as $crate::vm::Operation<_, _, _, _, 1>>::OPCODE),
                                }
                            };
                            ("ensure inverse of zero halts") => {
                                should_succeed &= !(*a).is_zero()
                            };
                            ("ensure quadratic nonresidues halt") => {
                                should_succeed &= (*a).sqrt().is_some()
                            };
                        }
                        // Check the conditions.
                        $( $( check_condition!($condition); )+ )?

                        // If `should_succeed` is `true`, compute the expected output.
                        let expected = match should_succeed {
                            true => Some(console::program::Literal::$output(a.$operate()$(.$unwrap())?)),
                            false => None
                        };

                        for mode_a in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                            // Initialize the operands.
                            let a = console::program::Literal::from_str(&format!("{a}"))?;

                            // Initialize the operands.
                            let first = circuit::program::Literal::from_str(&format!("{a}.{mode_a}"))?;

                            // If this iteration should succeed, ensure the evaluated and executed outputs match the expected output.
                            if should_succeed {
                                // Compute the evaluated output.
                                let candidate_a = <$operation as $crate::vm::Operation<_, _, _, _, 1>>::evaluate(&[a])?;
                                // Compute the executed output.
                                let candidate_b = <$operation as $crate::vm::Operation<_, _, _, _, 1>>::$execute(&[first])?;

                                // Ensure the outputs match.
                                assert_eq!(expected, Some(candidate_a));
                                // Ensure the outputs match.
                                assert_eq!(expected, Some(circuit::Eject::eject_value(&candidate_b)));

                            }
                            // If the sampled values overflow on evaluation, ensure it halts.
                            else {
                                // Halt the evaluation.
                                let result_a = std::panic::catch_unwind(|| <$operation as $crate::vm::Operation<_, _, _, _, 1>>::evaluate(&[a.clone()]).unwrap());
                                // Ensure the evaluation halted.
                                assert!(result_a.is_err(), "Failure case (on iteration {i}) did not halt (console): {a}");

                                // Halt the execution.
                                if mode_a.is_constant() {
                                    // Attempt to execute a failure case.
                                    let result_b = std::panic::catch_unwind(|| <$operation as $crate::vm::Operation<_, _, _, _, 1>>::$execute(&[first]).unwrap());
                                    // Ensure the execution halted.
                                    assert!(result_b.is_err(), "Failure case (on iteration {i}) did not halt (circuit): {a}");
                                } else {
                                    // Attempt to execute a failure case.
                                    let _result_b = <$operation as $crate::vm::Operation<_, _, _, _, 1>>::$execute(&[first])?;
                                    // Ensure the execution halted.
                                    assert!(!<CurrentAleo as circuit::Environment>::is_satisfied(), "Failure case (on iteration {i}) should not be satisfied (circuit): {a}");
                                }
                            }
                            // Reset the circuit.
                            <CurrentAleo as circuit::Environment>::reset();
                        }
                    }

                    Ok(())
                }
            }
        };

        // Case 1-A: Binary operation.
        // Case 1-B: Binary operation, where:
        //   1. "ensure overflow halts" | "ensure exponentiation overflow halts"
        //     - If the sampled values overflow on evaluation, ensure it halts.
        //     - If the sampled values **do not** overflow on evaluation, ensure it succeeds.
        //   2. "ensure divide by zero halts"
        //     - If the sampled divisor is zero, ensure it halts.
        //     - If the sampled divisor is **not** zero, ensure it succeeds.
        ($operator:tt::$operate:tt == $operation:tt::$execute:tt for ($input_a:ident, $input_b:ident) => $output:ident $( ($($condition:tt),+) )?) => {
            paste::paste! {
                #[test]
                fn [<test _ $operate _ $input_a:lower _ $input_b:lower _ into _ $output:lower>]() -> Result<()> {
                    // Ensure the expected output type is correct.
                    assert_eq!(
                        console::program::LiteralType::$output,
                        <$operation as $crate::vm::Operation<_, _, _, _, 2>>::output_type(&[console::program::LiteralType::$input_a.into(), console::program::LiteralType::$input_b.into()])?
                    );

                    // Determine the number of iterations to run, based on the opcode.
                    let num_iterations: u64 = match *<$operation as $crate::vm::Operation<_, _, _, _, 2>>::OPCODE {
                        "pow" | "pow.w" => 10,
                        _ => 100
                    };

                    // Check the operation on randomly-sampled values.
                    for i in 0..num_iterations {
                        // Sample the first and second value.
                        #[allow(deprecated)]
                        let (a, b) = match i {
                            0 => ($input_a::zero(), $input_b::zero()),
                            1 => ($input_a::<CurrentNetwork>::rand(&mut test_rng()), $input_b::zero()),
                            2 => ($input_a::zero(), $input_b::<CurrentNetwork>::rand(&mut test_rng())),
                            3.. => ($input_a::<CurrentNetwork>::rand(&mut test_rng()), $input_b::<CurrentNetwork>::rand(&mut test_rng()))
                        };

                        // Initialize an indicator whether the operation should succeed or not.
                        #[allow(unused_mut)]
                        let mut should_succeed = true;
                        /// A helper macro to check the conditions.
                        macro_rules! check_condition {
                            ("ensure overflows halt") => {
                                match *<$operation as $crate::vm::Operation<_, _, _, _, 2>>::OPCODE {
                                    "add" | "add.w" => should_succeed &= (*a).checked_add(*b).is_some(),
                                    "div" | "div.w" => should_succeed &= (*a).checked_div(*b).is_some(),
                                    "mul" | "mul.w" => should_succeed &= (*a).checked_mul(*b).is_some(),
                                    "sub" | "sub.w" => should_succeed &= (*a).checked_sub(*b).is_some(),
                                    _ => panic!("Unsupported test enforcement for '{}'", <$operation as $crate::vm::Operation<_, _, _, _, 2>>::OPCODE),
                                }
                            };
                            ("ensure exponentiation overflows halt") => {
                                should_succeed &= (*a).checked_pow((*b) as u32).is_some()
                            };
                            ("ensure divide by zero halt") => {
                                should_succeed &= (*b) != 0
                            };
                        }
                        // Check the conditions.
                        $( $( check_condition!($condition); )+ )?

                        // If `should_succeed` is `true`, compute the expected output.
                        let expected = match should_succeed {
                            true => Some(console::program::Literal::$output(a.$operate(&b))),
                            false => None
                        };

                        for mode_a in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                            for mode_b in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                                // Initialize the operands.
                                let a = console::program::Literal::from_str(&format!("{a}"))?;
                                let b = console::program::Literal::from_str(&format!("{b}"))?;

                                // Initialize the operands.
                                let first = circuit::program::Literal::from_str(&format!("{a}.{mode_a}"))?;
                                let second = circuit::program::Literal::from_str(&format!("{b}.{mode_b}"))?;

                                // If this iteration should succeed, ensure the evaluated and executed outputs match the expected output.
                                if should_succeed {
                                    // Compute the evaluated output.
                                    let candidate_a = <$operation as $crate::vm::Operation<_, _, _, _, 2>>::evaluate(&[a, b])?;
                                    // Compute the executed output.
                                    let candidate_b = <$operation as $crate::vm::Operation<_, _, _, _, 2>>::$execute(&[first, second])?;

                                    // Ensure the outputs match.
                                    assert_eq!(expected, Some(candidate_a));
                                    // Ensure the outputs match.
                                    assert_eq!(expected, Some(circuit::Eject::eject_value(&candidate_b)));

                                }
                                // If the sampled values overflow on evaluation, ensure it halts.
                                else {
                                    // Halt the evaluation.
                                    let result_a = std::panic::catch_unwind(|| <$operation as $crate::vm::Operation<_, _, _, _, 2>>::evaluate(&[a.clone(), b.clone()]).unwrap());
                                    // Ensure the evaluation halted.
                                    assert!(result_a.is_err(), "Failure case (on iteration {i}) did not halt (console): {a} {b}");

                                    // Halt the execution.
                                    if (mode_a.is_constant() && mode_b.is_constant()) {
                                        // Attempt to execute a failure case.
                                        let result_b = std::panic::catch_unwind(|| <$operation as $crate::vm::Operation<_, _, _, _, 2>>::$execute(&[first, second]).unwrap());
                                        // Ensure the execution halted.
                                        assert!(result_b.is_err(), "Failure case (on iteration {i}) did not halt (circuit): {a} {b}");
                                    } else {
                                        // Attempt to execute a failure case.
                                        let _result_b = <$operation as $crate::vm::Operation<_, _, _, _, 2>>::$execute(&[first, second])?;
                                        // Ensure the execution halted.
                                        assert!(!<CurrentAleo as circuit::Environment>::is_satisfied(), "Failure case (on iteration {i}) should not be satisfied (circuit): {a} {b}");
                                    }
                                }
                                // Reset the circuit.
                                <CurrentAleo as circuit::Environment>::reset();
                            }
                        }
                    }

                    Ok(())
                }
            }
        };
    }
}
