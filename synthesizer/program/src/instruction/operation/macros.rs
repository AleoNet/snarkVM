// Copyright (C) 2019-2023 Aleo Systems Inc.
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
        $vis struct $name<N: Network>(core::marker::PhantomData<N>);

        impl<N: Network> $crate::Operation<N, console::program::Literal<N>, console::program::LiteralType, $num_inputs> for $name<N> {
            /// The opcode of the operation.
            const OPCODE: $crate::Opcode = Opcode::Literal($opcode);

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
            fn execute<A: circuit::Aleo<Network = N>>(inputs: &[circuit::Literal<A>; $num_inputs]) -> Result<circuit::Literal<A>> {
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
                type Operation = $name::<CurrentNetwork>;
                // Execute the test cases for the operation.
                // $crate::test_execute!(Operator::$operate == Operation::execute { $( ( $($input),+ ) => $output $( ($($condition),+) )?, )+ });
            }
        }
    };
    // K-ary operation with question mark (?).
    ($vis:vis struct $name:ident<$operator:path, $circuit_operator:path, $operate:ident?, $opcode:tt, $num_inputs:tt> { $( ( $($input:ident),+ ) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
        /// The implementation of the binary operation.
        #[derive(Clone, PartialEq, Eq, Hash)]
        $vis struct $name<N: Network>(core::marker::PhantomData<N>);

        impl<N: Network> $crate::Operation<N, console::program::Literal<N>, console::program::LiteralType, $num_inputs> for $name<N> {
            /// The opcode of the operation.
            const OPCODE: $crate::Opcode = Opcode::Literal($opcode);

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
            fn execute<A: circuit::Aleo<Network = N>>(inputs: &[circuit::Literal<A>; $num_inputs]) -> Result<circuit::Literal<A>> {
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
                type Operation = $name::<CurrentNetwork>;
                // Execute the test cases for the operation.
                // $crate::test_execute!(Operator::$operate == Operation::execute? { $( ( $($input),+ ) => $output $( ($($condition),+) )?, )+ });
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
            $((console::program::Literal::$input_a(first), console::program::Literal::$input_b(second), console::program::Literal::$input_c(third)) => console::program::Literal::$output($operator::$operate(first, second, third)),)+
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
        let [first, second, third] = $inputs.to_owned();
        // Compute the output.
        match (first, second, third) {
            $((circuit::Literal::$input_a(first), circuit::Literal::$input_b(second), circuit::Literal::$input_c(third)) => circuit::Literal::$output($operator::$operate(&first, &second, &third)),)+
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
