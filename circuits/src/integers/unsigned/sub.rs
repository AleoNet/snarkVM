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

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Sub<Self> for Unsigned<E, U, SIZE> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self - &other
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Sub<&Self> for Unsigned<E, U, SIZE> {
    type Output = Self;

    fn sub(self, other: &Self) -> Self::Output {
        let flipped = Self::from_bits(other.bits_le.iter().map(|bit| !bit).collect());
        let mut one = Unsigned::new(Mode::Constant, U::one());
        self + &flipped.add(&one)
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Sub<Unsigned<E, U, SIZE>>
    for &Unsigned<E, U, SIZE>
{
    type Output = Unsigned<E, U, SIZE>;

    fn sub(self, other: Unsigned<E, U, SIZE>) -> Self::Output {
        (*self).clone() - other
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> Sub<&Unsigned<E, U, SIZE>>
    for &Unsigned<E, U, SIZE>
{
    type Output = Unsigned<E, U, SIZE>;

    fn sub(self, other: &Unsigned<E, U, SIZE>) -> Self::Output {
        (*self).clone() - other
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> SubAssign<Self> for Unsigned<E, U, SIZE> {
    fn sub_assign(&mut self, other: Self) {
        *self -= &other;
    }
}

impl<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize> SubAssign<&Self> for Unsigned<E, U, SIZE> {
    fn sub_assign(&mut self, other: &Self) {
        *self = self.clone() - other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use crate::integers::unsigned::test_utilities::check_operation;
    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 100;

    fn test_sub<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize>(
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

            let expected = first.wrapping_sub(&second);

            let name = format!("Sub: a - b {}", i);
            let compute_candidate = || {
                let a = Unsigned::<E, U, SIZE>::new(mode_a, first);
                let b = Unsigned::<E, U, SIZE>::new(mode_b, second);
                a - b
            };
            check_operation::<E, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    fn test_sub_assign<E: Environment, U: PrimitiveUnsignedInteger, const SIZE: usize>(
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

            let expected = first.wrapping_sub(&second);

            let name = format!("SubAssign: a -= b {}", i);
            let compute_candidate = || {
                let mut a = Unsigned::<E, U, SIZE>::new(mode_a, first);
                let b = Unsigned::<E, U, SIZE>::new(mode_b, second);
                a -= b;
                a
            };
            check_operation::<E, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    #[test]
    fn test_u8_sub_constant_constant() {
        test_sub::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((32, 0, 0, 0)));
        test_sub_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((32, 0, 0, 0)));
    }

    #[test]
    fn test_u8_sub_constant_public() {
        test_sub::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_sub_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u8_sub_constant_private() {
        test_sub::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_sub_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u8_sub_public_constant() {
        test_sub::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_sub_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u8_sub_public_public() {
        test_sub::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((10, 16, 75, 158)));
        test_sub_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((10, 16, 75, 158)));
    }

    #[test]
    fn test_u8_sub_public_private() {
        test_sub::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((10, 8, 83, 158)));
        test_sub_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((10, 8, 83, 158)));
    }

    #[test]
    fn test_u8_sub_private_constant() {
        test_sub::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_sub_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u8_sub_private_public() {
        test_sub::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((10, 8, 83, 158)));
        test_sub_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((10, 8, 83, 158)));
    }

    #[test]
    fn test_u8_sub_private_private() {
        test_sub::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((10, 0, 91, 158)));
        test_sub_assign::<Circuit, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((10, 0, 91, 158)));
    }

    // Tests for i16

    #[test]
    fn test_u16_sub_constant_constant() {
        test_sub::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((64, 0, 0, 0)));
        test_sub_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((64, 0, 0, 0)));
    }

    #[test]
    fn test_u16_sub_constant_public() {
        test_sub::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_sub_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u16_sub_constant_private() {
        test_sub::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_sub_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u16_sub_public_constant() {
        test_sub::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_sub_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u16_sub_public_public() {
        test_sub::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((18, 32, 155, 326)));
        test_sub_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((18, 32, 155, 326)));
    }

    #[test]
    fn test_u16_sub_public_private() {
        test_sub::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((18, 16, 171, 326)));
        test_sub_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((18, 16, 171, 326)));
    }

    #[test]
    fn test_u16_sub_private_constant() {
        test_sub::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_sub_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u16_sub_private_public() {
        test_sub::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((18, 16, 171, 326)));
        test_sub_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((18, 16, 171, 326)));
    }

    #[test]
    fn test_u16_sub_private_private() {
        test_sub::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((18, 0, 187, 326)));
        test_sub_assign::<Circuit, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((18, 0, 187, 326)));
    }

    // Tests for i32

    #[test]
    fn test_u32_sub_constant_constant() {
        test_sub::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((128, 0, 0, 0)));
        test_sub_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((128, 0, 0, 0)));
    }

    #[test]
    fn test_u32_sub_constant_public() {
        test_sub::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_sub_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u32_sub_constant_private() {
        test_sub::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_sub_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u32_sub_public_constant() {
        test_sub::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_sub_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u32_sub_public_public() {
        test_sub::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((34, 64, 315, 662)));
        test_sub_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((34, 64, 315, 662)));
    }

    #[test]
    fn test_u32_sub_public_private() {
        test_sub::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((34, 32, 347, 662)));
        test_sub_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((34, 32, 347, 662)));
    }

    #[test]
    fn test_u32_sub_private_constant() {
        test_sub::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_sub_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u32_sub_private_public() {
        test_sub::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((34, 32, 347, 662)));
        test_sub_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((34, 32, 347, 662)));
    }

    #[test]
    fn test_u32_sub_private_private() {
        test_sub::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((34, 0, 379, 662)));
        test_sub_assign::<Circuit, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((34, 0, 379, 662)));
    }

    // Tests for i64

    #[test]
    fn test_u64_sub_constant_constant() {
        test_sub::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((256, 0, 0, 0)));
        test_sub_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((256, 0, 0, 0)));
    }

    #[test]
    fn test_u64_sub_constant_public() {
        test_sub::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_sub_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u64_sub_constant_private() {
        test_sub::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_sub_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u64_sub_public_constant() {
        test_sub::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_sub_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u64_sub_public_public() {
        test_sub::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Public, Some((66, 128, 635, 1334)));
        test_sub_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Public, Some((66, 128, 635, 1334)));
    }

    #[test]
    fn test_u64_sub_public_private() {
        test_sub::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Private, Some((66, 64, 699, 1334)));
        test_sub_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Public, Mode::Private, Some((66, 64, 699, 1334)));
    }

    #[test]
    fn test_u64_sub_private_constant() {
        test_sub::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_sub_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u64_sub_private_public() {
        test_sub::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Public, Some((66, 64, 699, 1334)));
        test_sub_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Public, Some((66, 64, 699, 1334)));
    }

    #[test]
    fn test_u64_sub_private_private() {
        test_sub::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Private, Some((66, 0, 763, 1334)));
        test_sub_assign::<Circuit, u64, 64>(ITERATIONS, Mode::Private, Mode::Private, Some((66, 0, 763, 1334)));
    }

    // Tests for i128

    #[test]
    fn test_u128_sub_constant_constant() {
        test_sub::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((512, 0, 0, 0)));
        test_sub_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((512, 0, 0, 0)));
    }

    #[test]
    fn test_u128_sub_constant_public() {
        test_sub::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_sub_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_u128_sub_constant_private() {
        test_sub::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_sub_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_u128_sub_public_constant() {
        test_sub::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_sub_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_u128_sub_public_public() {
        test_sub::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Public, Some((130, 256, 1275, 2678)));
        test_sub_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Public, Some((130, 256, 1275, 2678)));
    }

    #[test]
    fn test_u128_sub_public_private() {
        test_sub::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Private, Some((130, 128, 1403, 2678)));
        test_sub_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Public, Mode::Private, Some((130, 128, 1403, 2678)));
    }

    #[test]
    fn test_u128_sub_private_constant() {
        test_sub::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_sub_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_u128_sub_private_public() {
        test_sub::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Public, Some((130, 128, 1403, 2678)));
        test_sub_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Public, Some((130, 128, 1403, 2678)));
    }

    #[test]
    fn test_u128_sub_private_private() {
        test_sub::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Private, Some((130, 0, 1531, 2678)));
        test_sub_assign::<Circuit, u128, 128>(ITERATIONS, Mode::Private, Mode::Private, Some((130, 0, 1531, 2678)));
    }
}
