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

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> LessThan<Self> for Unsigned<E, U, SIZE> {
    type Boolean = Boolean<E>;
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` is less than `other`.
    ///
    /// TODO (@pranav) Number of constraints.
    ///
    fn is_lt(&self, other: &Self) -> Self::Output {
        let mut result = Boolean::new(Mode::Constant, false);
        let mut prev_bits_equal = Boolean::new(Mode::Constant, true);

        for (self_bit, other_bit) in self.bits_le.iter().zip(other.bits_le.iter()).rev() {
            result = result.or(&prev_bits_equal.and(&(!self_bit).and(other_bit)));
            prev_bits_equal = prev_bits_equal.and(&!(self_bit.xor(other_bit)));
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use crate::integers::test_utilities::check_boolean_operation;
    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 100;

    fn test_is_lt<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize>(
        iterations: usize,
        mode_a: Mode,
        mode_b: Mode,
        circuit_properties: Option<(usize, usize, usize, usize)>,
    ) where
        Standard: Distribution<U>,
    {
        for i in 0..iterations {
            let first: U = UniformRand::rand(&mut thread_rng());
            let second: U = UniformRand::rand(&mut thread_rng());

            let expected = first < second;

            let name = format!("Less Than: a < b {}", i);
            let compute_candidate = || {
                let a = Unsigned::<E, U, SIZE>::new(mode_a, first);
                let b = Unsigned::<E, U, SIZE>::new(mode_b, second);
                a.is_lt(&b)
            };
            check_boolean_operation::<E>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    #[test]
    fn test_u8_is_lt_constant_constant() {
        test_is_lt::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((18, 0, 0, 0)));
    }

    #[test]
    fn test_u8_is_lt_constant_public() {
        test_is_lt::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u8_is_lt_constant_private() {
        test_is_lt::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u8_is_lt_public_constant() {
        test_is_lt::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u8_is_lt_public_public() {
        test_is_lt::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((2, 16, 37, 90)));
    }

    #[test]
    fn test_u8_is_lt_public_private() {
        test_is_lt::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((2, 8, 45, 90)));
    }

    #[test]
    fn test_u8_is_lt_private_constant() {
        test_is_lt::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u8_is_lt_private_public() {
        test_is_lt::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((2, 8, 45, 90)));
    }

    #[test]
    fn test_u8_is_lt_private_private() {
        test_is_lt::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((2, 0, 53, 90)));
    }

    // Tests for i16

    #[test]
    fn test_u16_is_lt_constant_constant() {
        test_is_lt::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((34, 0, 0, 0)));
    }

    #[test]
    fn test_u16_is_lt_constant_public() {
        test_is_lt::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u16_is_lt_constant_private() {
        test_is_lt::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u16_is_lt_public_constant() {
        test_is_lt::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u16_is_lt_public_public() {
        test_is_lt::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((2, 32, 77, 186)));
    }

    #[test]
    fn test_u16_is_lt_public_private() {
        test_is_lt::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((2, 16, 93, 186)));
    }

    #[test]
    fn test_u16_is_lt_private_constant() {
        test_is_lt::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u16_is_lt_private_public() {
        test_is_lt::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((2, 16, 93, 186)));
    }

    #[test]
    fn test_u16_is_lt_private_private() {
        test_is_lt::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((2, 0, 109, 186)));
    }

    // Tests for i32

    #[test]
    fn test_u32_is_lt_constant_constant() {
        test_is_lt::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((66, 0, 0, 0)));
    }

    #[test]
    fn test_u32_is_lt_constant_public() {
        test_is_lt::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u32_is_lt_constant_private() {
        test_is_lt::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u32_is_lt_public_constant() {
        test_is_lt::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u32_is_lt_public_public() {
        test_is_lt::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((2, 64, 157, 378)));
    }

    #[test]
    fn test_u32_is_lt_public_private() {
        test_is_lt::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((2, 32, 189, 378)));
    }

    #[test]
    fn test_u32_is_lt_private_constant() {
        test_is_lt::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u32_is_lt_private_public() {
        test_is_lt::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((2, 32, 189, 378)));
    }

    #[test]
    fn test_u32_is_lt_private_private() {
        test_is_lt::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((2, 0, 221, 378)));
    }

    // Tests for i64

    #[test]
    fn test_u64_is_lt_constant_constant() {
        test_is_lt::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((130, 0, 0, 0)));
    }

    #[test]
    fn test_u64_is_lt_constant_public() {
        test_is_lt::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u64_is_lt_constant_private() {
        test_is_lt::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u64_is_lt_public_constant() {
        test_is_lt::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u64_is_lt_public_public() {
        test_is_lt::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Public, Some((2, 128, 317, 762)));
    }

    #[test]
    fn test_u64_is_lt_public_private() {
        test_is_lt::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Private, Some((2, 64, 381, 762)));
    }

    #[test]
    fn test_u64_is_lt_private_constant() {
        test_is_lt::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u64_is_lt_private_public() {
        test_is_lt::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Public, Some((2, 64, 381, 762)));
    }

    #[test]
    fn test_u64_is_lt_private_private() {
        test_is_lt::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Private, Some((2, 0, 445, 762)));
    }

    // Tests for i128

    #[test]
    fn test_u128_is_lt_constant_constant() {
        test_is_lt::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((258, 0, 0, 0)));
    }

    #[test]
    fn test_u128_is_lt_constant_public() {
        test_is_lt::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u128_is_lt_constant_private() {
        test_is_lt::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u128_is_lt_public_constant() {
        test_is_lt::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u128_is_lt_public_public() {
        test_is_lt::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Public, Some((2, 256, 637, 1530)));
    }

    #[test]
    fn test_u128_is_lt_public_private() {
        test_is_lt::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Private, Some((2, 128, 765, 1530)));
    }

    #[test]
    fn test_u128_is_lt_private_constant() {
        test_is_lt::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u128_is_lt_private_public() {
        test_is_lt::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Public, Some((2, 128, 765, 1530)));
    }

    #[test]
    fn test_u128_is_lt_private_private() {
        test_is_lt::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Private, Some((2, 0, 893, 1530)));
    }
}
