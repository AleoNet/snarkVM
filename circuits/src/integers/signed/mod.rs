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
// pub mod double;
pub mod equal;
pub mod less_than;
// pub mod inv;
pub mod div;
pub mod mul;
//pub mod pow; TODO (@pranav)
pub mod neg;
// pub mod one;
pub mod sub;
pub mod ternary;
// pub mod zero;

use crate::{boolean::Boolean, traits::*, Environment, Mode, PrimitiveSignedInteger, PrimitiveUnsignedInteger};

use num_traits::real::Real;
use std::{
    fmt,
    marker::PhantomData,
    num::NonZeroUsize,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

pub type I8<E> = Signed<E, i8, u8, 8>;
pub type I16<E> = Signed<E, i16, u16, 16>;
pub type I32<E> = Signed<E, i32, u32, 32>;
pub type I64<E> = Signed<E, i64, u64, 64>;
pub type I128<E> = Signed<E, i128, u128, 128>;

#[derive(Clone)]
pub struct Signed<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> {
    bits_le: Vec<Boolean<E>>,
    phantom: PhantomData<(I, U)>,
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Signed<E, I, U, SIZE> {
    /// Initializes a new integer.
    pub fn new(mode: Mode, value: I) -> Self {
        if SIZE == 0 {
            E::halt("Signed must have a size greater than zero.")
        }

        let mut bits_le = Vec::with_capacity(SIZE);
        let mut value = value.to_le();
        for _ in 0..SIZE {
            bits_le.push(Boolean::new(mode, value & I::one() == I::one()));
            value = value >> 1;
        }
        Self {
            bits_le,
            phantom: Default::default(),
        }
    }

    // TODO: (@pranav) Implement From?
    /// Initialize a new integer from a vector of Booleans.
    fn from_bits(bits: Vec<Boolean<E>>) -> Self {
        if SIZE == 0 {
            E::halt("Signed must have a size greater than zero.")
        }
        if bits.len() != SIZE {
            E::halt("Incorrect number of bits to convert to Signed")
        }

        Self {
            bits_le: bits,
            phantom: Default::default(),
        }
    }

    /// Returns `true` if the integer is a constant.
    pub fn is_constant(&self) -> bool {
        self.bits_le.iter().all(|bit| bit.is_constant() == true)
    }

    /// Ejects the signed integer as a constant signed integer value.
    pub fn eject_value(&self) -> I {
        let base = if self.bits_le[SIZE - 1].eject_value() == true {
            I::min_value()
        } else {
            I::zero()
        };

        let mut magnitude = I::zero();

        for i in (0..(SIZE - 1)).rev() {
            // TODO (@pranav) This explicit cast could be eliminated by using a trait bound
            //  `bool: AsPrimitive<I>`. This however requires the trait bound to be expressed
            //  for every implementation of Signed that uses `eject_value` which looks unclean.
            let bit_value = if self.bits_le[i].eject_value() {
                I::one()
            } else {
                I::zero()
            };
            magnitude = (magnitude << 1) ^ bit_value;
        }
        base + magnitude
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> fmt::Debug
    for Signed<E, I, U, SIZE>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.eject_value())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Circuit;
    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };
    use snarkvm_utilities::UniformRand;

    const ITERATIONS: usize = 1000;

    fn run_test<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>(
        iterations: usize,
        mode: Mode,
    ) where
        Standard: Distribution<I>,
    {
        for _ in 0..iterations {
            let value: I = UniformRand::rand(&mut thread_rng());
            let integer = Signed::<Circuit, I, U, SIZE>::new(mode, value);
            assert_eq!(mode.is_constant(), integer.is_constant());
            assert_eq!(integer.eject_value(), value);
        }

        assert_eq!(
            Signed::<Circuit, I, U, SIZE>::new(mode, I::min_value()).eject_value(),
            I::min_value()
        );
        assert_eq!(
            Signed::<Circuit, I, U, SIZE>::new(mode, I::max_value()).eject_value(),
            I::max_value()
        );
    }

    #[test]
    fn test_i8() {
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant);
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public);
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private);
    }

    #[test]
    fn test_i16() {
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant);
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public);
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private);
    }

    #[test]
    fn test_i32() {
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant);
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public);
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private);
    }

    #[test]
    fn test_i64() {
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant);
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public);
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private);
    }

    #[test]
    fn test_i128() {
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant);
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public);
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private);
    }
}

#[cfg(test)]
pub mod test_utilities {
    use super::*;
    use crate::{Circuit, Environment, PrimitiveSignedInteger, PrimitiveUnsignedInteger};

    /// Checks that a given candidate gadget matches the expected result. Optionally checks
    /// that the number of constants, public variables, private variables, and constraints
    /// for the corresponding circuit matches some expected number.
    pub fn check_operation<
        E: Environment,
        I: PrimitiveSignedInteger,
        U: PrimitiveUnsignedInteger,
        const SIZE: usize,
    >(
        name: &str,
        expected: I,
        compute_candidate: &dyn Fn() -> Signed<E, I, U, SIZE>,
        circuit_properties: Option<(usize, usize, usize, usize)>,
    ) {
        E::scoped(name, |scope| {
            let candidate = compute_candidate();
            println!(
                "Constant: {:?}, Public: {:?}, Private: {:?}, Constraints: {:?}",
                scope.num_constants_in_scope(),
                scope.num_public_in_scope(),
                scope.num_private_in_scope(),
                scope.num_constraints_in_scope()
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
