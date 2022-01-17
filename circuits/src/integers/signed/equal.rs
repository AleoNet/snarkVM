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
        let all_bits_eq = self
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
    use crate::{integers::test_utilities::check_boolean_operation, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 100;

    fn test_is_eq<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>(
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

            let name = format!("Eq: a == b {}", i);
            let compute_candidate = || {
                let a = Signed::<E, I, U, SIZE>::new(mode_a, first);
                let b = Signed::<E, I, U, SIZE>::new(mode_b, second);
                a.is_eq(&b)
            };
            check_boolean_operation::<E>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    fn test_is_neq<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>(
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

            let expected = first != second;

            let name = format!("Neq: a != b {}", i);
            let compute_candidate = || {
                let a = Signed::<E, I, U, SIZE>::new(mode_a, first);
                let b = Signed::<E, I, U, SIZE>::new(mode_b, second);
                a.is_neq(&b)
            };
            check_boolean_operation::<E>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    #[test]
    fn test_i8_is_eq_constant_constant() {
        test_is_eq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((17, 0, 0, 0)));
        test_is_neq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((17, 0, 0, 0)));
    }

    #[test]
    fn test_i8_is_eq_constant_public() {
        test_is_eq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_is_neq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i8_is_eq_constant_private() {
        test_is_eq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_is_neq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i8_is_eq_public_constant() {
        test_is_eq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_is_neq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i8_is_eq_public_public() {
        test_is_eq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 16, 15, 46)));
        test_is_neq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 16, 15, 46)));
    }

    #[test]
    fn test_i8_is_eq_public_private() {
        test_is_eq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 8, 23, 46)));
        test_is_neq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 8, 23, 46)));
    }

    #[test]
    fn test_i8_is_eq_private_constant() {
        test_is_eq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_is_neq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i8_is_eq_private_public() {
        test_is_eq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 8, 23, 46)));
        test_is_neq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 8, 23, 46)));
    }

    #[test]
    fn test_i8_is_eq_private_private() {
        test_is_eq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 31, 46)));
        test_is_neq::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 31, 46)));
    }

    // Tests for i16

    #[test]
    fn test_i16_is_eq_constant_constant() {
        test_is_eq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((33, 0, 0, 0)));
        test_is_neq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((33, 0, 0, 0)));
    }

    #[test]
    fn test_i16_is_eq_constant_public() {
        test_is_eq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_is_neq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i16_is_eq_constant_private() {
        test_is_eq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_is_neq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i16_is_eq_public_constant() {
        test_is_eq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_is_neq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i16_is_eq_public_public() {
        test_is_eq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 32, 31, 94)));
        test_is_neq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 32, 31, 94)));
    }

    #[test]
    fn test_i16_is_eq_public_private() {
        test_is_eq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 16, 47, 94)));
        test_is_neq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 16, 47, 94)));
    }

    #[test]
    fn test_i16_is_eq_private_constant() {
        test_is_eq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_is_neq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i16_is_eq_private_public() {
        test_is_eq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 16, 47, 94)));
        test_is_neq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 16, 47, 94)));
    }

    #[test]
    fn test_i16_is_eq_private_private() {
        test_is_eq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 63, 94)));
        test_is_neq::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 63, 94)));
    }

    // Tests for i32

    #[test]
    fn test_i32_is_eq_constant_constant() {
        test_is_eq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((65, 0, 0, 0)));
        test_is_neq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((65, 0, 0, 0)));
    }

    #[test]
    fn test_i32_is_eq_constant_public() {
        test_is_eq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_is_neq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i32_is_eq_constant_private() {
        test_is_eq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_is_neq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i32_is_eq_public_constant() {
        test_is_eq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_is_neq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i32_is_eq_public_public() {
        test_is_eq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 64, 63, 190)));
        test_is_neq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 64, 63, 190)));
    }

    #[test]
    fn test_i32_is_eq_public_private() {
        test_is_eq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 32, 95, 190)));
        test_is_neq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 32, 95, 190)));
    }

    #[test]
    fn test_i32_is_eq_private_constant() {
        test_is_eq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_is_neq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i32_is_eq_private_public() {
        test_is_eq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 32, 95, 190)));
        test_is_neq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 32, 95, 190)));
    }

    #[test]
    fn test_i32_is_eq_private_private() {
        test_is_eq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 127, 190)));
        test_is_neq::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 127, 190)));
    }

    // Tests for i64

    #[test]
    fn test_i64_is_eq_constant_constant() {
        test_is_eq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((129, 0, 0, 0)));
        test_is_neq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((129, 0, 0, 0)));
    }

    #[test]
    fn test_i64_is_eq_constant_public() {
        test_is_eq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_is_neq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i64_is_eq_constant_private() {
        test_is_eq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_is_neq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i64_is_eq_public_constant() {
        test_is_eq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_is_neq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i64_is_eq_public_public() {
        test_is_eq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 128, 127, 382)));
        test_is_neq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 128, 127, 382)));
    }

    #[test]
    fn test_i64_is_eq_public_private() {
        test_is_eq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 64, 191, 382)));
        test_is_neq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 64, 191, 382)));
    }

    #[test]
    fn test_i64_is_eq_private_constant() {
        test_is_eq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_is_neq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i64_is_eq_private_public() {
        test_is_eq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 64, 191, 382)));
        test_is_neq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 64, 191, 382)));
    }

    #[test]
    fn test_i64_is_eq_private_private() {
        test_is_eq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 255, 382)));
        test_is_neq::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 255, 382)));
    }

    // Tests for i128

    #[test]
    fn test_i128_is_eq_constant_constant() {
        test_is_eq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((257, 0, 0, 0)));
        test_is_neq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((257, 0, 0, 0)));
    }

    #[test]
    fn test_i128_is_eq_constant_public() {
        test_is_eq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_is_neq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i128_is_eq_constant_private() {
        test_is_eq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_is_neq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i128_is_eq_public_constant() {
        test_is_eq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_is_neq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i128_is_eq_public_public() {
        test_is_eq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 256, 255, 766)));
        test_is_neq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 256, 255, 766)));
    }

    #[test]
    fn test_i128_is_eq_public_private() {
        test_is_eq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 128, 383, 766)));
        test_is_neq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 128, 383, 766)));
    }

    #[test]
    fn test_i128_is_eq_private_constant() {
        test_is_eq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_is_neq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i128_is_eq_private_public() {
        test_is_eq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 128, 383, 766)));
        test_is_neq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 128, 383, 766)));
    }

    #[test]
    fn test_i128_is_eq_private_private() {
        test_is_eq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 511, 766)));
        test_is_neq::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 511, 766)));
    }
}
