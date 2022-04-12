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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]

pub mod abs_checked;
pub mod abs_wrapped;
pub mod add_checked;
pub mod add_wrapped;
pub mod and;
pub mod compare;
pub mod div_checked;
pub mod div_wrapped;
pub mod equal;
pub mod from_bits;
pub mod msb;
pub mod mul_checked;
pub mod mul_wrapped;
pub mod neg;
pub mod not;
pub mod one;
pub mod or;
pub mod pow_checked;
pub mod pow_wrapped;
pub mod shl_checked;
pub mod shl_wrapped;
pub mod shr_checked;
pub mod shr_wrapped;
pub mod sub_checked;
pub mod sub_wrapped;
pub mod ternary;
pub mod to_bits;
pub mod to_field;
pub mod to_fields;
pub mod xor;
pub mod zero;

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

#[cfg(test)]
use snarkvm_circuits_environment::{
    assert_count,
    assert_count_fails,
    assert_output_mode,
    assert_scope,
    count,
    output_mode,
};

use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types_boolean::Boolean;
use snarkvm_circuits_types_field::Field;

use core::marker::PhantomData;

#[derive(Clone)]
pub struct Integer<E: Environment, I: IntegerType> {
    bits_le: Vec<Boolean<E>>,
    phantom: PhantomData<I>,
}

impl<E: Environment, I: IntegerType> IntegerTrait<I, U8<E>, U16<E>, U32<E>> for Integer<E, I> {}

impl<E: Environment, I: IntegerType> IntegerCore<I> for Integer<E, I> {}

impl<E: Environment, I: IntegerType> Inject for Integer<E, I> {
    type Primitive = I;

    /// Initializes a new integer.
    fn new(mode: Mode, value: Self::Primitive) -> Self {
        let mut bits_le = Vec::with_capacity(I::BITS);
        let mut value = value.to_le();
        for _ in 0..I::BITS {
            bits_le.push(Boolean::new(mode, value & I::one() == I::one()));
            value = value.wrapping_shr(1u32);
        }
        Self::from_bits_le(&bits_le)
    }
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
        self.bits_le.eject_mode()
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

impl<E: Environment, I: IntegerType> Parser for Integer<E, I> {
    type Environment = E;

    /// Parses a string into an integer circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the negative sign '-' from the string.
        let (string, negation) = map(opt(tag("-")), |neg: Option<&str>| neg.unwrap_or_default().to_string())(string)?;
        // Parse the digits from the string.
        let (string, primitive) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(string)?;
        // Combine the sign and primitive.
        let primitive = negation + primitive;
        // Parse the value from the string.
        let (string, value) = map_res(tag(Self::type_name()), |_| primitive.replace('_', "").parse())(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Self::new(mode, value))),
            None => Ok((string, Self::new(Mode::Constant, value))),
        }
    }
}

impl<E: Environment, I: IntegerType> TypeName for Integer<E, I> {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        I::type_name()
    }
}

impl<E: Environment, I: IntegerType> Debug for Integer<E, I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.eject_value())
    }
}

impl<E: Environment, I: IntegerType> Display for Integer<E, I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}.{}", self.eject_value(), Self::type_name(), self.eject_mode())
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
        let mut accumulator = E::zero();
        let mut coefficient = E::BaseField::one();
        for bit in &integer.bits_le {
            accumulator += LinearCombination::from(bit) * coefficient;
            coefficient = coefficient.double();
        }
        accumulator
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 100;

    fn check_new<I: IntegerType>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for _ in 0..ITERATIONS {
            let expected: I = UniformRand::rand(&mut test_rng());

            Circuit::scope(format!("New {mode}"), || {
                let candidate = Integer::<Circuit, I>::new(mode, expected);
                assert_eq!(mode, candidate.eject_mode());
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            })
        }
        // Check that the minimum and maximum integer bounds are correct.
        assert_eq!(I::MIN, Integer::<Circuit, I>::new(mode, I::MIN).eject_value());
        assert_eq!(I::MAX, Integer::<Circuit, I>::new(mode, I::MAX).eject_value());
    }

    fn check_parse<I: IntegerType>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for _ in 0..ITERATIONS {
            let value: I = UniformRand::rand(&mut test_rng());
            let expected = Integer::<Circuit, I>::new(mode, value);

            Circuit::scope(format!("Parse {mode}"), || {
                let (_, candidate) = Integer::<Circuit, I>::parse(&format!("{expected}")).unwrap();
                assert_eq!((mode, value), candidate.eject());
                assert_eq!(expected.eject_mode(), candidate.eject_mode());
                assert_eq!(expected.eject_value(), candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            })
        }
    }

    fn check_debug<I: IntegerType>() {
        // Constant
        let candidate = Integer::<Circuit, I>::new(Mode::Constant, I::one() + I::one());
        assert_eq!("2", format!("{:?}", candidate));

        // Public
        let candidate = Integer::<Circuit, I>::new(Mode::Public, I::one() + I::one());
        assert_eq!("2", format!("{:?}", candidate));

        // Private
        let candidate = Integer::<Circuit, I>::new(Mode::Private, I::one() + I::one());
        assert_eq!("2", format!("{:?}", candidate));
    }

    fn check_display<I: IntegerType>() {
        // Constant
        let candidate = Integer::<Circuit, I>::new(Mode::Constant, I::one() + I::one());
        assert_eq!(format!("2{}.constant", I::type_name()), format!("{}", candidate));

        // Public
        let candidate = Integer::<Circuit, I>::new(Mode::Public, I::one() + I::one());
        assert_eq!(format!("2{}.public", I::type_name()), format!("{}", candidate));

        // Private
        let candidate = Integer::<Circuit, I>::new(Mode::Private, I::one() + I::one());
        assert_eq!(format!("2{}.private", I::type_name()), format!("{}", candidate));
    }

    // u8

    #[test]
    fn test_u8_new() {
        check_new::<u8>(Mode::Constant, 8, 0, 0, 0);
        check_new::<u8>(Mode::Public, 0, 8, 0, 8);
        check_new::<u8>(Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_parse() {
        check_parse::<u8>(Mode::Constant, 8, 0, 0, 0);
        check_parse::<u8>(Mode::Public, 0, 8, 0, 8);
        check_parse::<u8>(Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_u8_debug_and_display() {
        check_debug::<u8>();
        check_display::<u8>();
    }

    // i8

    #[test]
    fn test_i8_new() {
        check_new::<i8>(Mode::Constant, 8, 0, 0, 0);
        check_new::<i8>(Mode::Public, 0, 8, 0, 8);
        check_new::<i8>(Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_parse() {
        check_parse::<i8>(Mode::Constant, 8, 0, 0, 0);
        check_parse::<i8>(Mode::Public, 0, 8, 0, 8);
        check_parse::<i8>(Mode::Private, 0, 0, 8, 8);
    }

    #[test]
    fn test_i8_debug_and_display() {
        check_debug::<i8>();
        check_display::<i8>();
    }

    // u16

    #[test]
    fn test_u16_new() {
        check_new::<u16>(Mode::Constant, 16, 0, 0, 0);
        check_new::<u16>(Mode::Public, 0, 16, 0, 16);
        check_new::<u16>(Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_parse() {
        check_parse::<u16>(Mode::Constant, 16, 0, 0, 0);
        check_parse::<u16>(Mode::Public, 0, 16, 0, 16);
        check_parse::<u16>(Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_u16_debug_and_display() {
        check_debug::<u16>();
        check_display::<u16>();
    }

    // i16

    #[test]
    fn test_i16_new() {
        check_new::<i16>(Mode::Constant, 16, 0, 0, 0);
        check_new::<i16>(Mode::Public, 0, 16, 0, 16);
        check_new::<i16>(Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_parse() {
        check_parse::<i16>(Mode::Constant, 16, 0, 0, 0);
        check_parse::<i16>(Mode::Public, 0, 16, 0, 16);
        check_parse::<i16>(Mode::Private, 0, 0, 16, 16);
    }

    #[test]
    fn test_i16_debug_and_display() {
        check_debug::<i16>();
        check_display::<i16>();
    }

    // u32

    #[test]
    fn test_u32_new() {
        check_new::<u32>(Mode::Constant, 32, 0, 0, 0);
        check_new::<u32>(Mode::Public, 0, 32, 0, 32);
        check_new::<u32>(Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_parse() {
        check_parse::<u32>(Mode::Constant, 32, 0, 0, 0);
        check_parse::<u32>(Mode::Public, 0, 32, 0, 32);
        check_parse::<u32>(Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_u32_debug_and_display() {
        check_debug::<u32>();
        check_display::<u32>();
    }

    // i32

    #[test]
    fn test_i32_new() {
        check_new::<i32>(Mode::Constant, 32, 0, 0, 0);
        check_new::<i32>(Mode::Public, 0, 32, 0, 32);
        check_new::<i32>(Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_parse() {
        check_parse::<i32>(Mode::Constant, 32, 0, 0, 0);
        check_parse::<i32>(Mode::Public, 0, 32, 0, 32);
        check_parse::<i32>(Mode::Private, 0, 0, 32, 32);
    }

    #[test]
    fn test_i32_debug_and_display() {
        check_debug::<i32>();
        check_display::<i32>();
    }

    // u64

    #[test]
    fn test_u64_new() {
        check_new::<u64>(Mode::Constant, 64, 0, 0, 0);
        check_new::<u64>(Mode::Public, 0, 64, 0, 64);
        check_new::<u64>(Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_parse() {
        check_parse::<u64>(Mode::Constant, 64, 0, 0, 0);
        check_parse::<u64>(Mode::Public, 0, 64, 0, 64);
        check_parse::<u64>(Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_u64_debug_and_display() {
        check_debug::<u64>();
        check_display::<u64>();
    }

    // i64

    #[test]
    fn test_i64_new() {
        check_new::<i64>(Mode::Constant, 64, 0, 0, 0);
        check_new::<i64>(Mode::Public, 0, 64, 0, 64);
        check_new::<i64>(Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_parse() {
        check_parse::<i64>(Mode::Constant, 64, 0, 0, 0);
        check_parse::<i64>(Mode::Public, 0, 64, 0, 64);
        check_parse::<i64>(Mode::Private, 0, 0, 64, 64);
    }

    #[test]
    fn test_i64_debug_and_display() {
        check_debug::<i64>();
        check_display::<i64>();
    }

    // u128

    #[test]
    fn test_u128_new() {
        check_new::<u128>(Mode::Constant, 128, 0, 0, 0);
        check_new::<u128>(Mode::Public, 0, 128, 0, 128);
        check_new::<u128>(Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_parse() {
        check_parse::<u128>(Mode::Constant, 128, 0, 0, 0);
        check_parse::<u128>(Mode::Public, 0, 128, 0, 128);
        check_parse::<u128>(Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_u128_debug_and_display() {
        check_debug::<u128>();
        check_display::<u128>();
    }

    // i128

    #[test]
    fn test_i128_new() {
        check_new::<i128>(Mode::Constant, 128, 0, 0, 0);
        check_new::<i128>(Mode::Public, 0, 128, 0, 128);
        check_new::<i128>(Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_parse() {
        check_parse::<i128>(Mode::Constant, 128, 0, 0, 0);
        check_parse::<i128>(Mode::Public, 0, 128, 0, 128);
        check_parse::<i128>(Mode::Private, 0, 0, 128, 128);
    }

    #[test]
    fn test_i128_debug_and_display() {
        check_debug::<i128>();
        check_display::<i128>();
    }
}

#[cfg(test)]
mod test_utilities {
    use core::{
        fmt::{Debug, Display},
        panic::UnwindSafe,
    };
    use snarkvm_circuits_environment::{assert_scope, assert_scope_fails, Circuit, Eject, Environment};

    pub fn check_operation_passes<V: Debug + Display + PartialEq, LHS, RHS, OUT: Eject<Primitive = V>>(
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
        Circuit::scope(name, || {
            let candidate = operation(a, b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);
            assert_scope!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    pub fn check_operation_passes_without_counts<
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
        Circuit::scope(name, || {
            let candidate = operation(a, b);
            assert_eq!(expected, candidate.eject_value(), "{} != {} := {}", expected, candidate.eject_value(), case);
        });
        Circuit::reset();
    }

    pub fn check_operation_fails<LHS, RHS, OUT>(
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
        Circuit::scope(name, || {
            let _candidate = operation(a, b);
            assert_scope_fails!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    pub fn check_operation_fails_without_counts<LHS, RHS, OUT>(
        name: &str,
        case: &str,
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT,
    ) {
        Circuit::scope(name, || {
            let _candidate = operation(a, b);
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
        Circuit::reset();
    }

    pub fn check_operation_halts<LHS: UnwindSafe, RHS: UnwindSafe, OUT>(
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
        Circuit::scope(name, || {
            let candidate = operation(input);
            assert_eq!(expected, candidate.eject_value(), "{}", case);
            assert_scope!(case, num_constants, num_public, num_private, num_constraints);
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
        Circuit::scope(name, || {
            let _candidate = operation(input);
            assert_scope_fails!(case, num_constants, num_public, num_private, num_constraints);
        });
        Circuit::reset();
    }

    pub fn check_unary_operation_halts<IN: UnwindSafe, OUT>(input: IN, operation: impl FnOnce(IN) -> OUT + UnwindSafe) {
        let result = std::panic::catch_unwind(|| operation(input));
        assert!(result.is_err());
    }
}
