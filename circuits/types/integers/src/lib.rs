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

mod helpers;
use helpers::IntegerCircuitType;

pub mod abs_checked;
pub mod abs_wrapped;
pub mod add_checked;
pub mod add_wrapped;
pub mod and;
pub mod div_checked;
pub mod div_wrapped;
pub mod equal;
pub mod greater_than;
pub mod greater_than_or_equal;
pub mod less_than;
pub mod less_than_or_equal;
pub mod mul_checked;
pub mod mul_wrapped;
pub mod neg;
pub mod not;
pub mod not_equal;
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
pub mod xor;

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
    assert_output_type,
    assert_scope,
    count,
    output_type,
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
        let mut bits_le = Vec::with_capacity(I::BITS as usize);
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

    const ITERATIONS: u64 = 100;

    fn check_new<I: IntegerType>(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
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
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
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
    use core::panic::UnwindSafe;

    /// A generic template for an integer test case.
    #[macro_export]
    macro_rules! test_integer_case {
        // Typical test instantiation (static).
        ($test_fn:ident, $primitive:ident, $description:ident) => {
            paste::paste! {
                #[test]
                fn [<test_ $primitive _ $description>]() {
                    $test_fn::<$primitive>();
                }
            }
        };
        // Typical test instantiation (unary).
        ($test_fn:ident, $primitive:ident, $mode:expr, $description:ident) => {
            paste::paste! {
                #[test]
                fn [<test_ $primitive _ $description>]() {
                    $test_fn::<$primitive>($mode);
                }
            }
        };
        // Typical test instantiation (binary).
        ($test_fn:ident, $primitive:ident, $mode_a:expr, $mode_b:expr, $description:ident) => {
            paste::paste! {
                #[test]
                fn [<test_ $primitive _ $description>]() {
                    $test_fn::<$primitive>($mode_a, $mode_b);
                }
            }
        };
        // Typical test instantiation (binary).
        ($test_fn:ident, $primitive_a:ident, $primitive_b:ident, $mode_a:expr, $mode_b:expr, $description:ident) => {
            paste::paste! {
                #[test]
                fn [<test_ $primitive_a _ $description _ $primitive_b>]() {
                    $test_fn::<$primitive_a, $primitive_b>($mode_a, $mode_b);
                }
            }
        };
        // Typical test instantiation (ternary).
        ($test_fn:ident, $primitive:ident, $mode_a:expr, $mode_b:expr, $mode_c:expr, $description:ident) => {
            paste::paste! {
                #[test]
                fn [<test_ $primitive _ $description>]() {
                    $test_fn::<$primitive>($mode_a, $mode_b, $mode_c);
                }
            }
        };
        // Typically used to ignore exhaustive tests by default (unary).
        (#[$meta:meta], $test_fn:ident, $primitive:ident, $mode:expr, $description:ident) => {
            paste::paste! {
                #[test]
                #[$meta]
                fn [<test_ $primitive _ $description>]() {
                    $test_fn::<$primitive>($mode);
                }
            }
        };
        // Typically used to ignore exhaustive tests by default (binary).
        (#[$meta:meta], $test_fn:ident, $primitive:ident, $mode_a:expr, $mode_b:expr, $description:ident) => {
            paste::paste! {
                #[test]
                #[$meta]
                fn [<test_ $primitive _ $description>]() {
                    $test_fn::<$primitive>($mode_a, $mode_b);
                }
            }
        };
        // Typically used to ignore exhaustive tests by default (binary).
        (#[$meta:meta], $test_fn:ident, $primitive_a:ident, $primitive_b:ident, $mode_a:expr, $mode_b:expr, $description:ident) => {
            paste::paste! {
                #[test]
                #[$meta]
                fn [<test_ $primitive_a _ $description _ $primitive_b>]() {
                    $test_fn::<$primitive_a, $primitive_b>($mode_a, $mode_b);
                }
            }
        };
        // Typically used to ignore exhaustive tests by default (ternary).
        (#[$meta:meta], $test_fn:ident, $primitive:ident, $mode_a:expr, $mode_b:expr, $mode_c:expr, $description:ident) => {
            paste::paste! {
                #[test]
                #[$meta]
                fn [<test_ $primitive _ $description>]() {
                    $test_fn::<$primitive>($mode_a, $mode_b, $mode_c);
                }
            }
        };
    }

    /// Invokes `test_integer_case!` on all combinations of `Mode`s.
    #[macro_export]
    macro_rules! test_integer_static {
        ($test_fn:ident, $primitive:ident, $description:ident) => {
            test_integer_case!($test_fn, $primitive, $description);
        };
    }

    /// Invokes `test_integer_case!` on all combinations of `Mode`s.
    #[macro_export]
    macro_rules! test_integer_unary {
        ($test_fn:ident, $primitive:ident, $description:ident) => {
            paste::paste! {
                test_integer_case!($test_fn, $primitive, Mode::Constant, [<$description _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, [<$description _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, [<$description _ private>]);
            }
        };
        (#[$meta:meta], $test_fn:ident, $primitive:ident, $description:ident, $variant:ident) => {
            paste::paste! {
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, [<$description _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, [<$description _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, [<$description _ private _ $variant>]);
            }
        };
    }

    /// Invokes `test_integer_case!` on all combinations of `Mode`s.
    #[macro_export]
    macro_rules! test_integer_binary {
        ($test_fn:ident, $primitive:ident, $description:ident) => {
            paste::paste! {
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Constant, [<constant _ $description _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Public, [<constant _ $description _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Private, [<constant _ $description _ private>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Constant, [<public _ $description _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Public, [<public _ $description _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Private, [<public _ $description _ private>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Constant, [<private _ $description _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Public, [<private _ $description _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Private, [<private _ $description _ private>]);
            }
        };
        ($test_fn:ident, $primitive_a:ident, $primitive_b:ident, $description:ident) => {
            paste::paste! {
                test_integer_case!($test_fn, $primitive_a, $primitive_b, Mode::Constant, Mode::Constant, [<constant _ $description _ constant>]);
                test_integer_case!($test_fn, $primitive_a, $primitive_b, Mode::Constant, Mode::Public, [<constant _ $description _ public>]);
                test_integer_case!($test_fn, $primitive_a, $primitive_b, Mode::Constant, Mode::Private, [<constant _ $description _ private>]);
                test_integer_case!($test_fn, $primitive_a, $primitive_b, Mode::Public, Mode::Constant, [<public _ $description _ constant>]);
                test_integer_case!($test_fn, $primitive_a, $primitive_b, Mode::Public, Mode::Public, [<public _ $description _ public>]);
                test_integer_case!($test_fn, $primitive_a, $primitive_b, Mode::Public, Mode::Private, [<public _ $description _ private>]);
                test_integer_case!($test_fn, $primitive_a, $primitive_b, Mode::Private, Mode::Constant, [<private _ $description _ constant>]);
                test_integer_case!($test_fn, $primitive_a, $primitive_b, Mode::Private, Mode::Public, [<private _ $description _ public>]);
                test_integer_case!($test_fn, $primitive_a, $primitive_b, Mode::Private, Mode::Private, [<private _ $description _ private>]);
            }
        };
        (#[$meta:meta], $test_fn:ident, $primitive:ident, $description:ident, $variant:ident) => {
            paste::paste! {
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Constant, [<constant _ $description _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Public, [<constant _ $description _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Private, [<constant _ $description _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Constant, [<public _ $description _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Public, [<public _ $description _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Private, [<public _ $description _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Constant, [<private _ $description _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Public, [<private _ $description _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Private, [<private _ $description _ private _ $variant>]);
            }
        };
        (#[$meta:meta], $test_fn:ident, $primitive_a:ident, $primitive_b:ident, $description:ident, $variant:ident) => {
            paste::paste! {
                test_integer_case!(#[$meta], $test_fn, $primitive_a, $primitive_b, Mode::Constant, Mode::Constant, [<constant _ $description _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive_a, $primitive_b, Mode::Constant, Mode::Public, [<constant _ $description _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive_a, $primitive_b, Mode::Constant, Mode::Private, [<constant _ $description _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive_a, $primitive_b, Mode::Public, Mode::Constant, [<public _ $description _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive_a, $primitive_b, Mode::Public, Mode::Public, [<public _ $description _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive_a, $primitive_b, Mode::Public, Mode::Private, [<public _ $description _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive_a, $primitive_b, Mode::Private, Mode::Constant, [<private _ $description _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive_a, $primitive_b, Mode::Private, Mode::Public, [<private _ $description _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive_a, $primitive_b, Mode::Private, Mode::Private, [<private _ $description _ private _ $variant>]);
            }
        };
    }

    /// Invokes `test_integer_case!` on all combinations of `Mode`s.
    #[macro_export]
    macro_rules! test_integer_ternary {
        ($test_fn:ident, $primitive:ident, $description_a:ident, $description_b:ident, $description_c:ident) => {
            paste::paste! {
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Constant, Mode::Constant, [<$description_a _ constant _ $description_b _ constant _ $description_c _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Constant, Mode::Public, [<$description_a _ constant _ $description_b _ constant _ $description_c _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Constant, Mode::Private, [<$description_a _ constant _ $description_b _ constant _ $description_c _ private>]);
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Public, Mode::Constant, [<$description_a _ constant _ $description_b _ public _ $description_c _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Public, Mode::Public, [<$description_a _ constant _ $description_b _ public _ $description_c _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Public, Mode::Private, [<$description_a _ constant _ $description_b _ public _ $description_c _ private>]);
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Private, Mode::Constant, [<$description_a _ constant _ $description_b _ private _ $description_c _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Private, Mode::Public, [<$description_a _ constant _ $description_b _ private _ $description_c _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Constant, Mode::Private, Mode::Private, [<$description_a _ constant _ $description_b _ private _ $description_c _ private>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Constant, Mode::Constant, [<$description_a _ public _ $description_b _ constant _ $description_c _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Constant, Mode::Public, [<$description_a _ public _ $description_b _ constant _ $description_c _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Constant, Mode::Private, [<$description_a _ public _ $description_b _ constant _ $description_c _ private>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Public, Mode::Constant, [<$description_a _ public _ $description_b _ public _ $description_c _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Public, Mode::Public, [<$description_a _ public _ $description_b _ public _ $description_c _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Public, Mode::Private, [<$description_a _ public _ $description_b _ public _ $description_c _ private>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Private, Mode::Constant, [<$description_a _ public _ $description_b _ private _ $description_c _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Private, Mode::Public, [<$description_a _ public _ $description_b _ private _ $description_c _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Public, Mode::Private, Mode::Private, [<$description_a _ public _ $description_b _ private _ $description_c _ private>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Constant, Mode::Constant, [<$description_a _ private _ $description_b _ constant _ $description_c _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Constant, Mode::Public, [<$description_a _ private _ $description_b _ constant _ $description_c _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Constant, Mode::Private, [<$description_a _ private _ $description_b _ constant _ $description_c _ private>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Public, Mode::Constant, [<$description_a _ private _ $description_b _ public _ $description_c _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Public, Mode::Public, [<$description_a _ private _ $description_b _ public _ $description_c _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Public, Mode::Private, [<$description_a _ private _ $description_b _ public _ $description_c _ private>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Private, Mode::Constant, [<$description_a _ private _ $description_b _ private _ $description_c _ constant>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Private, Mode::Public, [<$description_a _ private _ $description_b _ private _ $description_c _ public>]);
                test_integer_case!($test_fn, $primitive, Mode::Private, Mode::Private, Mode::Private, [<$description_a _ private _ $description_b _ private _ $description_c _ private>]);
            }
        };

        (#[$meta:meta], $test_fn:ident, $primitive:ident, $description_a:ident, $description_b:ident, $description_c:ident, $variant:ident) => {
            paste::paste! {
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Constant, Mode::Constant, [<$description_a _ constant _ $description_b _ constant _ $description_c _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Constant, Mode::Public, [<$description_a _ constant _ $description_b _ constant _ $description_c _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Constant, Mode::Private, [<$description_a _ constant _ $description_b _ constant _ $description_c _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Public, Mode::Constant, [<$description_a _ constant _ $description_b _ public _ $description_c _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Public, Mode::Public, [<$description_a _ constant _ $description_b _ public _ $description_c _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Public, Mode::Private, [<$description_a _ constant _ $description_b _ public _ $description_c _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Private, Mode::Constant, [<$description_a _ constant _ $description_b _ private _ $description_c _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Private, Mode::Public, [<$description_a _ constant _ $description_b _ private _ $description_c _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Constant, Mode::Private, Mode::Private, [<$description_a _ constant _ $description_b _ private _ $description_c _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Constant, Mode::Constant, [<$description_a _ public _ $description_b _ constant _ $description_c _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Constant, Mode::Public, [<$description_a _ public _ $description_b _ constant _ $description_c _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Constant, Mode::Private, [<$description_a _ public _ $description_b _ constant _ $description_c _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Public, Mode::Constant, [<$description_a _ public _ $description_b _ public _ $description_c _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Public, Mode::Public, [<$description_a _ public _ $description_b _ public _ $description_c _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Public, Mode::Private, [<$description_a _ public _ $description_b _ public _ $description_c _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Private, Mode::Constant, [<$description_a _ public _ $description_b _ private _ $description_c _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Private, Mode::Public, [<$description_a _ public _ $description_b _ private _ $description_c _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Public, Mode::Private, Mode::Private, [<$description_a _ public _ $description_b _ private _ $description_c _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Constant, Mode::Constant, [<$description_a _ private _ $description_b _ constant _ $description_c _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Constant, Mode::Public, [<$description_a _ private _ $description_b _ constant _ $description_c _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Constant, Mode::Private, [<$description_a _ private _ $description_b _ constant _ $description_c _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Public, Mode::Constant, [<$description_a _ private _ $description_b _ public _ $description_c _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Public, Mode::Public, [<$description_a _ private _ $description_b _ public _ $description_c _ public_ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Public, Mode::Private, [<$description_a _ private _ $description_b _ public _ $description_c _ private _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Private, Mode::Constant, [<$description_a _ private _ $description_b _ private _ $description_c _ constant _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Private, Mode::Public, [<$description_a _ private _ $description_b _ private _ $description_c _ public _ $variant>]);
                test_integer_case!(#[$meta], $test_fn, $primitive, Mode::Private, Mode::Private, Mode::Private, [<$description_a _ private _ $description_b _ private _ $description_c _ private _ $variant>]);
            }
        };
    }

    pub fn check_operation_halts<LHS: UnwindSafe, RHS: UnwindSafe, OUT>(
        a: LHS,
        b: RHS,
        operation: impl FnOnce(LHS, RHS) -> OUT + UnwindSafe,
    ) {
        let result = std::panic::catch_unwind(|| operation(a, b));
        assert!(result.is_err());
    }

    pub fn check_unary_operation_halts<IN: UnwindSafe, OUT>(input: IN, operation: impl FnOnce(IN) -> OUT + UnwindSafe) {
        let result = std::panic::catch_unwind(|| operation(input));
        assert!(result.is_err());
    }
}
