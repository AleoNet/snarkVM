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
use crate::{BaseField, One, RippleCarryAdder, Zero};
use num_traits::WrappingAdd;
use snarkvm_fields::PrimeField;
use std::num::Wrapping;

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Add<Self> for Unsigned<E, U, SIZE> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

// TODO (@pranav) Do we need to optimize the number of contraints generated?
//  This has the same implementation as signed addition? Can we dedup?
impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Add<&Self> for Unsigned<E, U, SIZE> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        // Determine the variable mode.
        let mode = match self.is_constant() && other.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        };

        // Directly compute the sum, check for overflow.
        let value = self.eject_value().wrapping_add(&other.eject_value());

        // If the resulting value is a constant, return it directly.
        if mode.is_constant() {
            return Unsigned::new(mode, value);
        }

        let mut bits = self.bits_le.add_bits(&other.bits_le);
        let _carry = bits.pop();

        assert_eq!(bits.len(), SIZE);

        for i in 0..SIZE {
            let mask = U::one() << i;
            let value_bit = Boolean::<E>::new(mode, value & mask == mask);
            value_bit.is_eq(&bits[i]);
        }

        Self::from_bits(bits)
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Add<Unsigned<E, U, SIZE>>
    for &Unsigned<E, U, SIZE>
{
    type Output = Unsigned<E, U, SIZE>;

    fn add(self, other: Unsigned<E, U, SIZE>) -> Self::Output {
        (*self).clone() + other
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Add<&Unsigned<E, U, SIZE>>
    for &Unsigned<E, U, SIZE>
{
    type Output = Unsigned<E, U, SIZE>;

    fn add(self, other: &Unsigned<E, U, SIZE>) -> Self::Output {
        (*self).clone() + other
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> AddAssign<Self> for Unsigned<E, U, SIZE> {
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> AddAssign<&Self> for Unsigned<E, U, SIZE> {
    fn add_assign(&mut self, other: &Self) {
        *self = self.clone() + other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{unsigned::test_utilities::check_operation, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };
    use std::num::Wrapping;

    const ITERATIONS: usize = 100;

    fn test_add<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize>(
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

            let expected = first.wrapping_add(&second);

            let name = format!("Add: a + b {}", i);
            let compute_candidate = || {
                let a = Unsigned::<E, U, SIZE>::new(mode_a, first);
                let b = Unsigned::<E, U, SIZE>::new(mode_b, second);
                a + b
            };
            check_operation::<E, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    fn test_add_assign<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize>(
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

            let expected = first.wrapping_add(&second);

            let name = format!("AddAssign: a += b {}", i);
            let compute_candidate = || {
                let mut a = Unsigned::<E, U, SIZE>::new(mode_a, first);
                let b = Unsigned::<E, U, SIZE>::new(mode_b, second);
                a += b;
                a
            };
            check_operation::<E, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    #[test]
    fn test_u8_add_constant_constant() {
        test_add::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((24, 0, 0, 0)));
        test_add_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((24, 0, 0, 0)));
    }

    #[test]
    fn test_u8_add_constant_public() {
        test_add::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_add_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u8_add_constant_private() {
        test_add::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_add_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u8_add_public_constant() {
        test_add::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_add_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u8_add_public_public() {
        test_add::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 16, 45, 106)));
        test_add_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 16, 45, 106)));
    }

    #[test]
    fn test_u8_add_public_private() {
        test_add::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 8, 53, 106)));
        test_add_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 8, 53, 106)));
    }

    #[test]
    fn test_u8_add_private_constant() {
        test_add::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_add_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u8_add_private_public() {
        test_add::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 8, 53, 106)));
        test_add_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 8, 53, 106)));
    }

    #[test]
    fn test_u8_add_private_private() {
        test_add::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 61, 106)));
        test_add_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 61, 106)));
    }

    // Tests for i16

    #[test]
    fn test_u16_add_constant_constant() {
        test_add::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((48, 0, 0, 0)));
        test_add_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((48, 0, 0, 0)));
    }

    #[test]
    fn test_u16_add_constant_public() {
        test_add::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_add_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u16_add_constant_private() {
        test_add::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_add_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u16_add_public_constant() {
        test_add::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_add_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u16_add_public_public() {
        test_add::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 32, 93, 218)));
        test_add_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 32, 93, 218)));
    }

    #[test]
    fn test_u16_add_public_private() {
        test_add::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 16, 109, 218)));
        test_add_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 16, 109, 218)));
    }

    #[test]
    fn test_u16_add_private_constant() {
        test_add::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_add_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u16_add_private_public() {
        test_add::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 16, 109, 218)));
        test_add_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 16, 109, 218)));
    }

    #[test]
    fn test_u16_add_private_private() {
        test_add::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 125, 218)));
        test_add_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 125, 218)));
    }

    // Tests for i32

    #[test]
    fn test_u32_add_constant_constant() {
        test_add::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((96, 0, 0, 0)));
        test_add_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((96, 0, 0, 0)));
    }

    #[test]
    fn test_u32_add_constant_public() {
        test_add::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_add_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u32_add_constant_private() {
        test_add::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_add_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u32_add_public_constant() {
        test_add::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_add_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u32_add_public_public() {
        test_add::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 64, 189, 442)));
        test_add_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 64, 189, 442)));
    }

    #[test]
    fn test_u32_add_public_private() {
        test_add::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 32, 221, 442)));
        test_add_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 32, 221, 442)));
    }

    #[test]
    fn test_u32_add_private_constant() {
        test_add::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_add_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u32_add_private_public() {
        test_add::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 32, 221, 442)));
        test_add_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 32, 221, 442)));
    }

    #[test]
    fn test_u32_add_private_private() {
        test_add::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 253, 442)));
        test_add_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 253, 442)));
    }

    // Tests for i64

    #[test]
    fn test_u64_add_constant_constant() {
        test_add::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((192, 0, 0, 0)));
        test_add_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((192, 0, 0, 0)));
    }

    #[test]
    fn test_u64_add_constant_public() {
        test_add::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_add_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u64_add_constant_private() {
        test_add::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_add_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u64_add_public_constant() {
        test_add::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_add_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u64_add_public_public() {
        test_add::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 128, 381, 890)));
        test_add_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 128, 381, 890)));
    }

    #[test]
    fn test_u64_add_public_private() {
        test_add::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 64, 445, 890)));
        test_add_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 64, 445, 890)));
    }

    #[test]
    fn test_u64_add_private_constant() {
        test_add::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_add_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u64_add_private_public() {
        test_add::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 64, 445, 890)));
        test_add_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 64, 445, 890)));
    }

    #[test]
    fn test_u64_add_private_private() {
        test_add::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 509, 890)));
        test_add_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 509, 890)));
    }

    // Tests for i128

    #[test]
    fn test_u128_add_constant_constant() {
        test_add::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((384, 0, 0, 0)));
        test_add_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((384, 0, 0, 0)));
    }

    #[test]
    fn test_u128_add_constant_public() {
        test_add::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_add_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u128_add_constant_private() {
        test_add::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_add_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u128_add_public_constant() {
        test_add::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_add_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u128_add_public_public() {
        test_add::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 256, 765, 1786)));
        test_add_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Public, Some((1, 256, 765, 1786)));
    }

    #[test]
    fn test_u128_add_public_private() {
        test_add::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 128, 893, 1786)));
        test_add_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Private, Some((1, 128, 893, 1786)));
    }

    #[test]
    fn test_u128_add_private_constant() {
        test_add::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_add_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u128_add_private_public() {
        test_add::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 128, 893, 1786)));
        test_add_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Public, Some((1, 128, 893, 1786)));
    }

    #[test]
    fn test_u128_add_private_private() {
        test_add::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 1021, 1786)));
        test_add_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Private, Some((1, 0, 1021, 1786)));
    }
}
