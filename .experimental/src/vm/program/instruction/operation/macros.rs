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
    ($vis:vis struct $name:ident<$operator:path, $operate:ident, $opcode:tt> { $( ($input_a:ident, $input_b:ident) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
        /// The implementation of the binary operation.
        #[derive(Clone, PartialEq, Eq, Hash)]
        $vis struct $name<N: Network, A: circuit::Aleo>(core::marker::PhantomData<(N, A)>);

        impl<N: Network, A: circuit::Aleo> $crate::vm::Operation<N, console::program::Literal<N>, circuit::Literal<A>, console::program::LiteralType, 2> for $name<N, A> {
            /// The opcode of the operation.
            const OPCODE: $crate::vm::Opcode = Opcode::Literal($opcode);

            /// Returns the result of evaluating the operation on the given inputs.
            #[inline]
            fn evaluate(inputs: &[console::program::Literal<N>; 2]) -> Result<console::program::Literal<N>> {
                // Prepare the operator.
                use $operator as Operator;
                // Compute the output.
                Ok($crate::evaluate!(match Operator::$operate(inputs) { $( ($input_a, $input_b) => $output, )+ }))
            }

            /// Returns the result of executing the operation on the given circuit inputs.
            #[inline]
            fn execute(inputs: &[circuit::Literal<A>; 2]) -> Result<circuit::Literal<A>> {
                // Prepare the operator.
                use $operator as Operator;
                // Compute the output.
                Ok($crate::execute!(match Operator::$operate(inputs) { $( ($input_a, $input_b) => $output, )+ }))
            }

            /// Returns the output type from the given input types.
            #[inline]
            fn output_type(inputs: &[console::program::LiteralType; 2]) -> Result<console::program::LiteralType> {
                // Compute the output type.
                Ok($crate::output_type!(match inputs { $( ($input_a, $input_b) => $output, )+ }))
            }
        }

        paste::paste! {
            #[cfg(test)]
            mod [<test _ $operate>] {
                use super::$name;
                use console::network::prelude::*;
                // Prepare the operator.
                use $operator as Operator;
                // Evaluate the test cases for the operation.
                $crate::test_evaluate!(Operator::$operate == $name::evaluate { $( ($input_a, $input_b) => $output $( ($($condition),+) )?, )+ });
                // Execute the test cases for the operation.
                $crate::test_execute!(Operator::$operate == $name::execute { $( ($input_a, $input_b) => $output $( ($($condition),+) )?, )+ });
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
    (match $operator:tt::$operate:tt($inputs:expr) { $( ($input_a:ident, $input_b:ident) => $output:ident, )+ }) => {{
        // Retrieve the first and second operands.
        let [first, second] = $inputs;
        // Compute the output.
        match (first, second) {
            $((console::program::Literal::$input_a(first), console::program::Literal::$input_b(second)) => console::program::Literal::$output(first.$operate(second)),)+
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
    // Binary operation.
    (match $operator:tt::$operate:tt($inputs:expr) { $( ($input_a:ident, $input_b:ident) => $output:ident, )+ }) => {{
        // Retrieve the first and second operands.
        let [first, second] = $inputs;
        // Compute the output.
        match (first, second) {
            $((circuit::Literal::$input_a(first), circuit::Literal::$input_b(second)) => circuit::Literal::$output(first.$operate(second)),)+
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
            $((console::program::LiteralType::$input_a, console::program::LiteralType::$input_b) => console::program::LiteralType::$output,)+
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
        ($operator:tt::$operate:tt == $operation:tt::$evaluate:tt { $( ($input_a:ident, $input_b:ident) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
            // For each given case of inputs and outputs, invoke `Case 1A` or `Case 1B` (see below).
            $( $crate::test_evaluate!{$operator::$operate == $operation::$evaluate for ($input_a, $input_b) => $output $( ($($condition),+) )?} )+

            // For each non-existent case of inputs and outputs, invoke the following test to ensure the operation **fails**.
            paste::paste! {
                #[test]
                fn [<test _ $evaluate _ $operate _ fails _ on _ invalid _ operands>]() -> Result<()> {
                    use console::types::*;

                    type CurrentNetwork = console::network::Testnet3;
                    type CurrentAleo = circuit::network::AleoV0;

                    for i in 0..100 {
                        for literal_a in $crate::sample_literals!(CurrentNetwork, &mut test_rng()).iter() {
                            for literal_b in $crate::sample_literals!(CurrentNetwork, &mut test_rng()).iter() {
                                // Retrieve the types of the literals.
                                let (type_a, type_b) = (literal_a.to_type(), literal_b.to_type());

                                // Skip this iteration, if this is **not** an invalid operand case.
                                $(if type_a == console::program::LiteralType::$input_a && type_b == console::program::LiteralType::$input_b {
                                    continue;
                                })+

                                // Initialize the operands.
                                let first = console::program::Literal::from_str(&format!("{literal_a}"))?;
                                let second = console::program::Literal::from_str(&format!("{literal_b}"))?;

                                // Attempt to compute the invalid operand case.
                                let result = <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::$evaluate(&[first, second]);

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
        // Case 1B: Binary operation, where:
        //   1. "ensure overflow halts"
        //     - If the sampled values overflow on evaluation, ensure it halts.
        //     - If the sampled values **do not** overflow on evaluation, ensure it succeeds.
        //   2. "ensure divide by zero halts"
        //     - If the sampled divisor is zero, ensure it halts.
        //     - If the sampled divisor is **not** zero, ensure it succeeds.
        ($operator:tt::$operate:tt == $operation:tt::$evaluate:tt for ($input_a:ident, $input_b:ident) => $output:ident $( ($($condition:tt),+) )?) => {
            paste::paste! {
                #[test]
                fn [<test _ $evaluate _ $operate _ $input_a:lower _ $input_b:lower _ into _ $output:lower>]() -> Result<()> {
                    use console::types::*;

                    type CurrentNetwork = console::network::Testnet3;
                    type CurrentAleo = circuit::network::AleoV0;

                    // Ensure the expected output type is correct.
                    assert_eq!(
                        console::program::LiteralType::from(console::program::LiteralType::$output),
                        <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::output_type(&[console::program::LiteralType::$input_a.into(), console::program::LiteralType::$input_b.into()])?
                    );

                    // Check the operation on randomly-sampled values.
                    for i in 0..1_000u64 {
                        // Sample the first and second value.
                        #[allow(deprecated)]
                        let (a, b) = match i {
                            0 => ($input_a::zero(), $input_b::zero()),
                            1 => {
                                let a = $input_a::<CurrentNetwork>::rand(&mut test_rng());
                                (a, $input_b::zero())
                            },
                            2 => {
                                let b = $input_b::<CurrentNetwork>::rand(&mut test_rng());
                                ($input_a::zero(), b)
                            },
                            3.. => {
                                let a = $input_a::<CurrentNetwork>::rand(&mut test_rng());
                                let b = $input_b::<CurrentNetwork>::rand(&mut test_rng());
                                (a, b)
                            }
                        };

                        // Initialize the operands.
                        let first = console::program::Literal::from_str(&format!("{a}"))?;
                        let second = console::program::Literal::from_str(&format!("{b}"))?;

                        // Initialize an indicator whether the operation should succeed or not.
                        #[allow(unused_mut)]
                        let mut should_succeed = true;
                        $( $({
                            if $condition == "ensure overflows halt" {
                                match *<$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::OPCODE {
                                    "add" | "add.w" => should_succeed &= (*a).checked_add(*b).is_some(),
                                    "div" | "div.w" => should_succeed &= (*a).checked_div(*b).is_some(),
                                    "mul" | "mul.w" => should_succeed &= (*a).checked_mul(*b).is_some(),
                                    "sub" | "sub.w" => should_succeed &= (*a).checked_sub(*b).is_some(),
                                    _ => panic!("Unsupported test enforcement for '{}'", <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::OPCODE),
                                }
                            }
                            if $condition == "ensure divide by zero halts" {
                                should_succeed &= (*a).checked_div(*b).is_some();
                            }
                        })+ )?

                        // Skip this iteration, if this is **not** an overflow case.
                        match should_succeed {
                            // If the sampled values **do not** overflow on evaluation, ensure it succeeds.
                            true => {
                                // Compute the outputs.
                                let expected = console::program::Literal::$output(a.$operate(&b));
                                let candidate = <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::$evaluate(&[first, second])?;
                                // Ensure the outputs match.
                                assert_eq!(expected, candidate);
                            },
                            // If the sampled values overflow on evaluation, ensure it halts.
                            false => {
                                // Attempt to compute the overflow case.
                                let result = std::panic::catch_unwind(|| <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::$evaluate(&[first, second]));
                                // Ensure the computation halted.
                                assert!(result.is_err(), "Failure case (on iteration {i}) did not halt: {a} {b}");
                            }
                        }
                    }

                    Ok(())
                }
            }
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
        // Case 1: Binary operation.
        ($operator:tt::$operate:tt == $operation:tt::$execute:tt { $( ($input_a:ident, $input_b:ident) => $output:ident $( ($($condition:tt),+) )?, )+ }) => {
            // For each given case of inputs and outputs, invoke `Case 1A` or `Case 1B` (see below).
            $( $crate::test_execute!{$operator::$operate == $operation::$execute for ($input_a, $input_b) => $output $( ($($condition),+) )?} )+

            // For each non-existent case of inputs and outputs, invoke the following test to ensure the operation **fails**.
            paste::paste! {
                #[test]
                fn [<test _ $execute _ $operate _ fails _ on _ invalid _ operands>]() -> Result<()> {
                    use console::types::*;

                    type CurrentNetwork = console::network::Testnet3;
                    type CurrentAleo = circuit::network::AleoV0;

                    for i in 0..10 {
                        for literal_a in $crate::sample_literals!(CurrentNetwork, &mut test_rng()).iter() {
                            for literal_b in $crate::sample_literals!(CurrentNetwork, &mut test_rng()).iter() {
                                for mode_a in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                                    for mode_b in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                                        // Retrieve the types of the literals.
                                        let (type_a, type_b) = (literal_a.to_type(), literal_b.to_type());

                                        // Skip this iteration, if this is **not** an invalid operand case.
                                        $(if type_a == console::program::LiteralType::$input_a && type_b == console::program::LiteralType::$input_b {
                                            continue;
                                        })+

                                        // Initialize the operands.
                                        let first = circuit::program::Literal::from_str(&format!("{literal_a}.{mode_a}"))?;
                                        let second = circuit::program::Literal::from_str(&format!("{literal_b}.{mode_b}"))?;

                                        // Attempt to compute the invalid operand case.
                                        let result = <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::$execute(&[first, second]);

                                        // Ensure the computation failed.
                                        assert!(result.is_err(), "An invalid operands case (on iteration {i}) did not fail: {literal_a} {literal_b}");

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

        // Case 1A: Binary operation.
        // Case 1B: Binary operation, where:
        //   1. "ensure overflow halts"
        //     - If the sampled values overflow on evaluation, ensure it halts.
        //     - If the sampled values **do not** overflow on evaluation, ensure it succeeds.
        //   2. "ensure divide by zero halts"
        //     - If the sampled divisor is zero, ensure it halts.
        //     - If the sampled divisor is **not** zero, ensure it succeeds.
        ($operator:tt::$operate:tt == $operation:tt::$execute:tt for ($input_a:ident, $input_b:ident) => $output:ident $( ($($condition:tt),+) )?) => {
            paste::paste! {
                #[test]
                fn [<test _ $execute _ $operate _ $input_a:lower _ $input_b:lower _ into _ $output:lower>]() -> Result<()> {
                    use console::types::*;

                    type CurrentNetwork = console::network::Testnet3;
                    type CurrentAleo = circuit::network::AleoV0;

                    // Ensure the expected output type is correct.
                    assert_eq!(
                        console::program::LiteralType::from(console::program::LiteralType::$output),
                        <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::output_type(&[console::program::LiteralType::$input_a.into(), console::program::LiteralType::$input_b.into()])?
                    );

                    // Check the operation on randomly-sampled values.
                    for i in 0..50u64 {
                        for mode_a in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                            for mode_b in &[circuit::Mode::Constant, circuit::Mode::Public, circuit::Mode::Private] {
                                // Sample the first and second value.
                                #[allow(deprecated)]
                                let (a, b) = match i {
                                    0 => ($input_a::zero(), $input_b::zero()),
                                    1 => {
                                        let a = $input_a::<CurrentNetwork>::rand(&mut test_rng());
                                        (a, $input_b::zero())
                                    },
                                    2 => {
                                        let b = $input_b::<CurrentNetwork>::rand(&mut test_rng());
                                        ($input_a::zero(), b)
                                    },
                                    3.. => {
                                        let a = $input_a::<CurrentNetwork>::rand(&mut test_rng());
                                        let b = $input_b::<CurrentNetwork>::rand(&mut test_rng());
                                        (a, b)
                                    }
                                };

                                // Initialize the operands.
                                let first = circuit::program::Literal::from_str(&format!("{a}.{mode_a}"))?;
                                let second = circuit::program::Literal::from_str(&format!("{b}.{mode_b}"))?;

                                // Initialize an indicator whether the operation should succeed or not.
                                #[allow(unused_mut)]
                                let mut should_succeed = true;
                                $( $({
                                    if $condition == "ensure overflows halt" {
                                        match *<$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::OPCODE {
                                            "add" | "add.w" => should_succeed &= (*a).checked_add(*b).is_some(),
                                            "div" | "div.w" => should_succeed &= (*a).checked_div(*b).is_some(),
                                            "mul" | "mul.w" => should_succeed &= (*a).checked_mul(*b).is_some(),
                                            "sub" | "sub.w" => should_succeed &= (*a).checked_sub(*b).is_some(),
                                            _ => panic!("Unsupported test enforcement for '{}'", <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::OPCODE),
                                        }
                                    }
                                    if $condition == "ensure divide by zero halts" {
                                        should_succeed &= (*a).checked_div(*b).is_some();
                                    }
                                })+ )?

                                // Skip this iteration, if this is **not** an overflow case.
                                match should_succeed {
                                    // If the sampled values **do not** overflow on evaluation, ensure it succeeds.
                                    true => {
                                        // Compute the outputs.
                                        let expected = console::program::Literal::$output(a.$operate(&b));
                                        let candidate = <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::$execute(&[first, second])?;

                                        use circuit::Eject;

                                        // Ensure the outputs match.
                                        assert_eq!(expected, candidate.eject_value());
                                    },
                                    // If the sampled values overflow on evaluation, ensure it halts.
                                    false => if (mode_a.is_constant() && mode_b.is_constant()) {
                                        // Attempt to compute the overflow case.
                                        let result = std::panic::catch_unwind(|| <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::$execute(&[first, second]));
                                        // Ensure the computation halted.
                                        assert!(result.is_err(), "Failure case (on iteration {i}) did not halt: {a} {b}");
                                    } else {
                                        // Attempt to compute the overflow case.
                                        let _result = <$operation::<CurrentNetwork, CurrentAleo> as $crate::vm::Operation<_, _, _, _, 2>>::$execute(&[first, second]);
                                        // Ensure the computation halted.
                                        assert!(!<CurrentAleo as circuit::Environment>::is_satisfied(), "Failure case (on iteration {i}) did not halt: {a} {b}");
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
