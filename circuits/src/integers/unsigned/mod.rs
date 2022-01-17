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
pub mod div;
pub mod equal;
pub mod less_than;
pub mod sub;
pub mod ternary;

use crate::{boolean::Boolean, traits::*, Environment, Mode, PrimitiveUnsignedInteger};

use std::{
    fmt,
    marker::PhantomData,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

pub type U8<E> = Unsigned<E, u8, 8>;
pub type U16<E> = Unsigned<E, u16, 16>;
pub type U32<E> = Unsigned<E, u32, 32>;
pub type U64<E> = Unsigned<E, u64, 64>;
pub type U128<E> = Unsigned<E, u128, 128>;

#[derive(Clone)]
pub struct Unsigned<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> {
    pub(crate) bits_le: Vec<Boolean<E>>,
    phantom: PhantomData<U>,
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Unsigned<E, U, SIZE> {
    /// Initializes a new integer.
    pub fn new(mode: Mode, value: U) -> Self {
        let mut bits_le = Vec::with_capacity(SIZE);
        let mut value = value.to_le();
        for _ in 0..SIZE {
            bits_le.push(Boolean::new(mode, value & U::one() == U::one()));
            value = value >> 1;
        }
        Self {
            bits_le,
            phantom: Default::default(),
        }
    }

    // TODO: (@pranav) Implement From?
    /// Initialize a new integer from a vector of Booleans.
    pub(crate) fn from_bits(bits: Vec<Boolean<E>>) -> Self {
        if bits.len() != SIZE {
            E::halt("Incorrect number of bits to convert to Signed")
        } else {
            Self {
                bits_le: bits,
                phantom: Default::default(),
            }
        }
    }

    /// Returns `true` if the integer is a constant.
    pub fn is_constant(&self) -> bool {
        self.bits_le.iter().all(|bit| bit.is_constant() == true)
    }

    /// Ejects the unsigned integer as a constant unsigned integer value.
    pub fn eject_value(&self) -> U {
        self.bits_le.iter().rev().fold(U::zero(), |value, bit| {
            // TODO (@pranav) This explicit cast could be eliminated by using a trait bound
            //  `bool: AsPrimitive<I>`. This however requires the trait bound to be expressed
            //  for every implementation of Signed that uses `eject_value` which feels unclean.
            let bit_value = if bit.eject_value() { U::one() } else { U::zero() };
            (value << 1) ^ bit_value
        })
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> fmt::Debug for Unsigned<E, U, SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.eject_value())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };
    use snarkvm_utilities::UniformRand;

    const ITERATIONS: usize = 1000;

    fn run_test<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize>(iterations: usize, mode: Mode)
    where
        Standard: Distribution<U>,
    {
        for _ in 0..iterations {
            let value: U = UniformRand::rand(&mut thread_rng());
            let integer = Unsigned::<Circuit, U, SIZE>::new(mode, value);
            assert_eq!(mode.is_constant(), integer.is_constant());
            assert_eq!(integer.eject_value(), value);
        }

        assert_eq!(
            Unsigned::<Circuit, U, SIZE>::new(mode, U::min_value()).eject_value(),
            U::min_value()
        );
        assert_eq!(
            Unsigned::<Circuit, U, SIZE>::new(mode, U::max_value()).eject_value(),
            U::max_value()
        );
    }

    #[test]
    fn test_i8() {
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Constant);
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Public);
        run_test::<Circuit, u8, 8>(ITERATIONS, Mode::Private);
    }

    #[test]
    fn test_i16() {
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Constant);
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Public);
        run_test::<Circuit, u16, 16>(ITERATIONS, Mode::Private);
    }

    #[test]
    fn test_i32() {
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Constant);
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Public);
        run_test::<Circuit, u32, 32>(ITERATIONS, Mode::Private);
    }

    #[test]
    fn test_i64() {
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Constant);
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Public);
        run_test::<Circuit, u64, 64>(ITERATIONS, Mode::Private);
    }

    #[test]
    fn test_i128() {
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Constant);
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Public);
        run_test::<Circuit, u128, 128>(ITERATIONS, Mode::Private);
    }
}

#[cfg(test)]
pub mod test_utilities {
    use super::*;
    use crate::{Environment, PrimitiveUnsignedInteger};

    /// Checks that a given candidate gadget matches the expected result. Optionally checks
    /// that the number of constants, public variables, private variables, and constraints
    /// for the corresponding circuit matches some expected number.
    pub fn check_operation<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize>(
        name: &str,
        expected: U,
        compute_candidate: &dyn Fn() -> Unsigned<E, U, SIZE>,
        circuit_properties: Option<(usize, usize, usize, usize)>,
    ) {
        E::scoped(name, |scope| {
            let candidate = compute_candidate();
            println!(
                "Constant: {:?}, Public: {:?}, Private: {:?}, Constraints: {:?}",
                scope.num_constants_in_scope(),
                scope.num_public_in_scope(),
                scope.num_private_in_scope(),
                scope.num_constraints_in_scope(),
            );
            assert_eq!(expected, candidate.eject_value());
            if let Some((num_constants, num_public, num_private, num_constraints)) = circuit_properties {
                assert_eq!(num_constants, scope.num_constants_in_scope());
                assert_eq!(num_public, scope.num_public_in_scope());
                assert_eq!(num_private, scope.num_private_in_scope());
                assert_eq!(num_constraints, scope.num_constraints_in_scope());
            }
            assert!(E::is_satisfied());
        });
    }
}
