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

use super::*;
use itertools::all;

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Equal<Self>
    for Signed<E, I, U, SIZE>
{
    type Boolean = Boolean<E>;
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    /// TODO (@pranav) Number of constraints; Is extra logical and for Boolean::new(Mode::Constant, true) free?
    ///
    fn is_eq(&self, other: &Self) -> Self::Output {
        let mut all_bits_eq = self
            .bits_le
            .iter()
            .zip(other.bits_le.iter())
            .map(|(self_bit, other_bit)| self_bit.is_eq(other_bit));
        all_bits_eq.fold(Boolean::new(Mode::Constant, true), |prev_bits_eq, next_bit_eq| {
            prev_bits_eq.and(&next_bit_eq)
        })
    }

    ///
    /// Returns `true` if `self` and `other` are *not* equal.
    ///
    /// This method constructs a boolean that indicates if
    /// `self` and `other ` are *not* equal to each other.
    ///
    /// This method costs 8 constraints.
    ///
    fn is_neq(&self, other: &Self) -> Self::Output {
        !self.is_eq(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 100;

    fn run_test<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>(
        iterations: usize,
        mode_a: Mode,
        mode_b: Mode,
        circuit_properties: Option<(usize, usize, usize, usize)>,
    ) where
        Standard: Distribution<I>,
    {
        for i in 0..iterations {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());
            let expected = first == second;

            let a = Signed::<Circuit, I, U, SIZE>::new(mode_a, first);
            let b = Signed::<Circuit, I, U, SIZE>::new(mode_b, second);

            Circuit::scoped(&format!("Equals {}", i), |scope| {
                let equals = a.is_eq(&b);
                assert_eq!(expected, equals.eject_value());
                if let Some((num_constants, num_public, num_private, num_constraints)) = circuit_properties {
                    assert_eq!(num_constants, scope.num_constants_in_scope());
                    assert_eq!(num_public, scope.num_public_in_scope());
                    assert_eq!(num_private, scope.num_private_in_scope());
                    assert_eq!(num_constraints, scope.num_constraints_in_scope());
                }
                Circuit::is_satisfied();
            });

            Circuit::scoped(&format!("Not Equals {}", i), |scope| {
                let not_equals = a.is_neq(&b);
                assert_eq!(expected, !(not_equals.eject_value()));
                if let Some((num_constants, num_public, num_private, num_constraints)) = circuit_properties {
                    assert_eq!(num_constants, scope.num_constants_in_scope());
                    assert_eq!(num_public, scope.num_public_in_scope());
                    assert_eq!(num_private, scope.num_private_in_scope());
                    assert_eq!(num_constraints, scope.num_constraints_in_scope());
                }
                Circuit::is_satisfied();
            });
        }
    }

    #[test]
    fn test_i8_is_eq_all_modes() {
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((8, 0, 0, 0)));
        run_test::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((8, 0, 0, 0)));
    }

    #[test]
    fn test_i16_is_eq_all_modes() {
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((16, 0, 0, 0)));
        run_test::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((16, 0, 0, 0)));
    }

    #[test]
    fn test_i32_is_eq_all_modes() {
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((32, 0, 0, 0)));
        run_test::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((32, 0, 0, 0)));
    }

    #[test]
    fn test_i64_is_eq_all_modes() {
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Private, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Public, Some((64, 0, 0, 0)));
        run_test::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Private, Some((64, 0, 0, 0)));
    }

    #[test]
    fn test_i128_is_eq_all_modes() {
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Private, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Public, Some((128, 0, 0, 0)));
        run_test::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Private, Some((128, 0, 0, 0)));
    }
}
