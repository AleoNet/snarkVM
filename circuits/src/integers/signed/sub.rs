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

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Sub<Self>
    for Signed<E, I, U, SIZE>
{
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self - &other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Sub<&Self>
    for Signed<E, I, U, SIZE>
{
    type Output = Self;

    fn sub(self, other: &Self) -> Self::Output {
        self + -other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>
    Sub<Signed<E, I, U, SIZE>> for &Signed<E, I, U, SIZE>
{
    type Output = Signed<E, I, U, SIZE>;

    fn sub(self, other: Signed<E, I, U, SIZE>) -> Self::Output {
        (*self).clone() - other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>
    Sub<&Signed<E, I, U, SIZE>> for &Signed<E, I, U, SIZE>
{
    type Output = Signed<E, I, U, SIZE>;

    fn sub(self, other: &Signed<E, I, U, SIZE>) -> Self::Output {
        (*self).clone() - other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> SubAssign<Self>
    for Signed<E, I, U, SIZE>
{
    fn sub_assign(&mut self, other: Self) {
        *self -= &other;
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> SubAssign<&Self>
    for Signed<E, I, U, SIZE>
{
    fn sub_assign(&mut self, other: &Self) {
        *self = self.clone() + -other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use crate::integers::signed::test_utilities::check_operation;
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

            let expected = first.wrapping_sub(&second);
            let a = Signed::<E, I, U, SIZE>::new(mode_a, first);
            let b = Signed::<E, I, U, SIZE>::new(mode_b, second);

            let name = format!("Sub: a - b {}", i);
            let compute_candidate = || &a - &b;
            check_operation::<E, I, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);

            let name = format!("SubAssign: a -= b {}", i);
            let compute_candidate = || {
                let mut candidate = (&a).clone();
                candidate -= &b;
                candidate
            };
            check_operation::<E, I, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    #[test]
    fn test_i8_sub_all_modes() {
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
    fn test_i16_sub_all_modes() {
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
    fn test_i32_sub_all_modes() {
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
    fn test_i64_sub_all_modes() {
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
    fn test_i128_sub_all_modes() {
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

    #[test]
    fn test_sub_matches() {
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());
            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };

            // Constant
            let first_signed = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let second_signed = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);
            let candidate_a = first_signed - second_signed;
            assert_eq!(expected, candidate_a.eject_value());

            // Private
            let first_signed = Signed::<Circuit, i64, u64, 64>::new(Mode::Private, first);
            let second_signed = Signed::<Circuit, i64, u64, 64>::new(Mode::Private, second);
            let candidate_b = first_signed - second_signed;
            assert_eq!(expected, candidate_b.eject_value());
        }
    }
}
