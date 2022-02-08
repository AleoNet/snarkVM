// Copyright (C) 2019-2021 Aleo Systems Inc.
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

pub mod add;
pub mod add_checked;
pub mod add_wrapped;
pub mod bitand;
pub mod bitor;
pub mod bitxor;
pub mod div;
pub mod div_checked;
pub mod div_wrapped;
pub mod equal;
pub mod from_bits;
pub mod mul;
pub mod mul_checked;
pub mod mul_wrapped;
pub mod neg;
pub mod not;
pub mod one;
pub mod pow_checked;
pub mod pow_wrapped;
pub mod shl;
pub mod shl_checked;
pub mod shl_wrapped;
pub mod shr;
pub mod shr_checked;
pub mod shr_wrapped;
pub mod sub;
pub mod sub_checked;
pub mod sub_wrapped;
pub mod ternary;
pub mod to_bits;
pub mod zero;

mod helpers;

use crate::{
    boolean::Boolean,
    fields::BaseField,
    helpers::integers::*,
    traits::*,
    Environment,
    LinearCombination,
    Mode,
};

use snarkvm_fields::PrimeField;
use std::{
    fmt,
    marker::PhantomData,
    ops::{
        Add,
        AddAssign,
        BitAnd,
        BitAndAssign,
        BitOr,
        BitOrAssign,
        BitXor,
        BitXorAssign,
        Div,
        DivAssign,
        Mul,
        MulAssign,
        Neg,
        Not,
        Shl,
        ShlAssign,
        Shr,
        ShrAssign,
        Sub,
        SubAssign,
    },
};

pub type I8<E> = Integer<E, i8>;
pub type I16<E> = Integer<E, i16>;
pub type I32<E> = Integer<E, i32>;
pub type I64<E> = Integer<E, i64>;
pub type I128<E> = Integer<E, i128>;

pub type U8<E> = Integer<E, u8>;
pub type U16<E> = Integer<E, u16>;
pub type U32<E> = Integer<E, u32>;
pub type U64<E> = Integer<E, u64>;
pub type U128<E> = Integer<E, u128>;

#[derive(Clone)]
pub struct Integer<E: Environment, I: IntegerType> {
    bits_le: Vec<Boolean<E>>,
    phantom: PhantomData<I>,
}

impl<E: Environment, I: IntegerType> IntegerTrait<E, I> for Integer<E, I> {
    /// Initializes a new integer.
    fn new(mode: Mode, value: I) -> Self {
        let mut bits_le = Vec::with_capacity(I::BITS);
        let mut value = value.to_le();
        for _ in 0..I::BITS {
            bits_le.push(Boolean::new(mode, value & I::one() == I::one()));
            value = value.wrapping_shr(1u32);
        }
        Self::from_bits_le(mode, &bits_le)
    }
}

// TODO (@pranav) Is there a better place for this?
/// Sealed trait pattern to prevent abuse of Magnitude.
mod private {
    use crate::helpers::integers::IntegerType;
    use num_traits::{ToPrimitive, Unsigned};

    /// Trait for integers that can be used as an unsigned magnitude.
    /// `Magnitude`s are either used to represent an integer exponent
    /// or the right operand in integer shift operations.
    pub trait Magnitude: IntegerType + ToPrimitive + Unsigned {}
    impl Magnitude for u8 {}
    impl Magnitude for u16 {}
    impl Magnitude for u32 {}
}

// TODO (@pranav) Document
impl<E: Environment, I: IntegerType> Integer<E, I> {
    fn cast_as_dual(self) -> Integer<E, I::Dual> {
        Integer::<E, I::Dual> { bits_le: self.bits_le, phantom: Default::default() }
    }
}

impl<E: Environment, I: IntegerType> Eject for Integer<E, I> {
    type Primitive = I;

    ///
    /// Ejects the mode of the integer.
    ///
    fn eject_mode(&self) -> Mode {
        let mut integer_mode = Mode::Constant;

        for bit_mode in self.bits_le.iter().map(Eject::eject_mode) {
            // // Check if the mode in the current iteration matches the integer mode.
            // if integer_mode != bit_mode {
            //     // If they do not match, the integer mode must be a constant.
            //     // Otherwise, this is a malformed integer, and the program should halt.
            //     match integer_mode == Mode::Constant {
            //         true => integer_mode = bit_mode,
            //         false => Circuit::halt("Detected an integer with a malformed mode"),
            //     }
            // }
            // TODO (@pranav) verify that this logic is safe.
            // The mode of an integer is determined by the following cases:
            //   - If there exists a bit with Mode::Private, then the integer's mode is Mode::Private.
            //   - If there exists no bits with Mode::Private and there exists one bit with Mode::Public,
            //     then the integer's mode is Mode::Public.
            //   - Otherwise, the integer's mode is Mode::Constant
            match (integer_mode, bit_mode) {
                (Mode::Constant, Mode::Public) | (Mode::Constant, Mode::Private) | (Mode::Public, Mode::Private) => {
                    integer_mode = bit_mode
                }
                (_, _) => (), // Do nothing.
            }
        }
        integer_mode
    }

    ///
    /// Ejects the integer as a constant integer value.
    ///
    fn eject_value(&self) -> Self::Primitive {
        self.bits_le.iter().rev().fold(I::zero(), |value, bit| match bit.eject_value() {
            true => (value.wrapping_shl(1)) ^ I::one(),
            false => (value.wrapping_shl(1)) ^ I::zero(),
        })
    }
}

impl<E: Environment, I: IntegerType> fmt::Debug for Integer<E, I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.eject_value())
    }
}

impl<E: Environment, I: IntegerType> From<Integer<E, I>> for LinearCombination<E::BaseField> {
    fn from(integer: Integer<E, I>) -> Self {
        From::from(&integer)
    }
}

impl<E: Environment, I: IntegerType> From<&Integer<E, I>> for LinearCombination<E::BaseField> {
    fn from(integer: &Integer<E, I>) -> Self {
        // Reconstruct the bits as a linear combination representing the original field value.
        let mut accumulator: LinearCombination<_> = BaseField::<E>::zero().into();
        let mut coefficient = BaseField::one();
        for bit in &integer.bits_le {
            accumulator += LinearCombination::from(BaseField::from(bit) * &coefficient);
            coefficient = coefficient.double();
        }
        accumulator
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 1000;

    fn check_new<I: IntegerType, IC: IntegerTrait<Circuit, I>>(mode: Mode) {
        let expected: I = UniformRand::rand(&mut thread_rng());
        let candidate = IC::new(mode, expected);
        assert_eq!(mode.is_constant(), candidate.is_constant());
        assert_eq!(candidate.eject_value(), expected);
    }

    fn check_min_max<I: IntegerType, IC: IntegerTrait<Circuit, I>>(mode: Mode) {
        assert_eq!(I::MIN, IC::new(mode, I::MIN).eject_value());
        assert_eq!(I::MAX, IC::new(mode, I::MAX).eject_value());
    }

    fn run_test<I: IntegerType>() {
        for _ in 0..ITERATIONS {
            check_new::<I, Integer<Circuit, I>>(Mode::Constant);
            check_new::<I, Integer<Circuit, I>>(Mode::Public);
            check_new::<I, Integer<Circuit, I>>(Mode::Private);
        }

        check_min_max::<I, Integer<Circuit, I>>(Mode::Constant);
        check_min_max::<I, Integer<Circuit, I>>(Mode::Public);
        check_min_max::<I, Integer<Circuit, I>>(Mode::Private);
    }

    #[test]
    fn test_i8() {
        run_test::<i8>();
    }

    #[test]
    fn test_i16() {
        run_test::<i16>();
    }

    #[test]
    fn test_i32() {
        run_test::<i32>();
    }

    #[test]
    fn test_i64() {
        run_test::<i64>();
    }

    #[test]
    fn test_i128() {
        run_test::<i128>();
    }

    #[test]
    fn test_u8() {
        run_test::<u8>();
    }

    #[test]
    fn test_u16() {
        run_test::<u16>();
    }

    #[test]
    fn test_u32() {
        run_test::<u32>();
    }

    #[test]
    fn test_u64() {
        run_test::<u64>();
    }

    #[test]
    fn test_u128() {
        run_test::<u128>();
    }
}

#[cfg(test)]
mod test_utilities {
    use crate::{helpers::integers::IntegerType, Circuit, Eject, Environment, IntegerTrait};
    use std::{
        fmt::{Debug, Display},
        panic::UnwindSafe,
    };

    pub fn check_binary_operation_passes<V: Debug + Display + PartialEq, LHS, RHS, OUT: Eject<Primitive = V>>(
        name: &str,
        case: &str,
        expected: V,
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = operation(a, b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);

            print!("Constants: {:?}, ", Circuit::num_constants_in_scope());
            print!("Public: {:?}, ", Circuit::num_public_in_scope());
            print!("Private: {:?}, ", Circuit::num_private_in_scope());
            print!("Constraints: {:?}\n", Circuit::num_constraints_in_scope());

            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
        Circuit::reset();
    }

    pub fn check_binary_operation_passes_without_expected_numbers<
        V: Debug + Display + PartialEq,
        LHS,
        RHS,
        OUT: Eject<Primitive = V>,
    >(
        name: &str,
        case: &str,
        expected: V,
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT,
    ) {
        Circuit::scoped(name, || {
            let candidate = operation(a, b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);
        });
        Circuit::reset();
    }

    pub fn check_binary_operation_fails<LHS, RHS, OUT>(
        name: &str,
        case: &str,
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = operation(a, b);

            print!("Constants: {:?}, ", Circuit::num_constants_in_scope());
            print!("Public: {:?}, ", Circuit::num_public_in_scope());
            print!("Private: {:?}, ", Circuit::num_private_in_scope());
            print!("Constraints: {:?}\n", Circuit::num_constraints_in_scope());

            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
        Circuit::reset();
    }

    pub fn check_binary_operation_fails_without_expected_numbers<LHS, RHS, OUT>(
        name: &str,
        case: &str,
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT,
    ) {
        Circuit::scoped(name, || {
            let candidate = operation(a, b);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
        Circuit::reset();
    }

    pub fn check_binary_operation_halts<LHS: UnwindSafe, RHS: UnwindSafe, OUT>(
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT + UnwindSafe,
    ) {
        let result = std::panic::catch_unwind(|| operation(a, b));
        assert!(result.is_err());
    }

    pub fn check_unary_operation_passes<V: Debug + Display + PartialEq, IN, OUT: Eject<Primitive = V>>(
        name: &str,
        case: &str,
        expected: V,
        input: IN,
        operation: impl FnOnce(IN) -> OUT,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = operation(input);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);

            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
        Circuit::reset();
    }

    pub fn check_unary_operation_passes_without_expected_numbers<
        V: Debug + Display + PartialEq,
        IN,
        OUT: Eject<Primitive = V>,
    >(
        name: &str,
        case: &str,
        expected: V,
        input: IN,
        operation: impl FnOnce(IN) -> OUT,
    ) {
        Circuit::scoped(name, || {
            let candidate = operation(input);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
        Circuit::reset();
    }

    pub fn check_unary_operation_fails<IN, OUT>(
        name: &str,
        case: &str,
        input: IN,
        operation: impl FnOnce(IN) -> OUT,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let candidate = operation(input);
            assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
        Circuit::reset();
    }

    pub fn check_unary_operation_fails_without_expected_numbers<IN, OUT>(
        name: &str,
        case: &str,
        input: IN,
        operation: impl FnOnce(IN) -> OUT,
    ) {
        Circuit::scoped(name, || {
            let candidate = operation(input);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
        Circuit::reset();
    }

    pub fn check_unary_operation_halts<IN: UnwindSafe, OUT>(input: IN, operation: impl FnOnce(IN) -> OUT + UnwindSafe) {
        let result = std::panic::catch_unwind(|| operation(input));
        assert!(result.is_err());
    }
}
