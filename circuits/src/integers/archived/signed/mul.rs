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

use super::*;
use crate::{RippleCarryAdder, SignExtend};

use std::iter;

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Mul<Self>
    for Signed<E, I, U, SIZE>
{
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        self * &other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Mul<&Self>
    for Signed<E, I, U, SIZE>
{
    type Output = Self;

    fn mul(self, other: &Self) -> Self::Output {
        // Determine the variable mode.
        let mode = match self.is_constant() && other.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        };

        // Directly compute the product, wrapping if necessary.
        let value = self.eject_value().wrapping_mul(&other.eject_value());

        if mode.is_constant() {
            return Signed::new(mode, value);
        }

        // pseudocode:
        //
        // res = 0;
        // for (i, bit) in other.bits.enumerate() {
        //   shifted_self = self << i;
        //
        //   if bit {
        //     res += shifted_self;
        //   }
        // }
        // return res

        // Sign extend to double precision
        let a = Boolean::sign_extend(&self.bits_le, SIZE * 2);
        let b = Boolean::sign_extend(&other.bits_le, SIZE * 2);

        let mut bits = vec![Boolean::new(mode, false); SIZE];

        // Compute double and mul algorithm
        let mut to_mul = Vec::new();
        let mut a_shifted = Vec::new();
        for (i, b_bit) in b.iter().enumerate() {
            // double
            a_shifted.extend(iter::repeat(Boolean::new(mode, false)).take(i));
            a_shifted.extend_from_slice(&a);
            a_shifted.truncate(SIZE);

            // conditionally mul
            to_mul.reserve(a_shifted.len());
            for a_bit in a_shifted.iter() {
                let selected_bit = Boolean::ternary(b_bit, a_bit, &Boolean::new(mode, false));

                to_mul.push(selected_bit);
            }

            bits = bits.add_bits(&to_mul);
            let _carry = bits.pop();
            to_mul.clear();
            a_shifted.clear();
        }
        drop(to_mul);
        drop(a_shifted);

        // Truncate the bits to the size of the integer
        bits.truncate(SIZE);

        // Check that the computed result matches the expected one.
        for i in 0..SIZE {
            let mask = I::one() << i;
            let value_bit = Boolean::<E>::new(mode, value & mask == mask);
            value_bit.is_eq(&bits[i]);
        }

        Signed::from_bits(bits)
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>
    Mul<Signed<E, I, U, SIZE>> for &Signed<E, I, U, SIZE>
{
    type Output = Signed<E, I, U, SIZE>;

    fn mul(self, other: Signed<E, I, U, SIZE>) -> Self::Output {
        (*self).clone() * other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>
    Mul<&Signed<E, I, U, SIZE>> for &Signed<E, I, U, SIZE>
{
    type Output = Signed<E, I, U, SIZE>;

    fn mul(self, other: &Signed<E, I, U, SIZE>) -> Self::Output {
        (*self).clone() * other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> MulAssign<Self>
    for Signed<E, I, U, SIZE>
{
    fn mul_assign(&mut self, other: Self) {
        *self *= &other;
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> MulAssign<&Self>
    for Signed<E, I, U, SIZE>
{
    fn mul_assign(&mut self, other: &Self) {
        *self = self.clone() * other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{integers::signed::test_utilities::check_operation, Circuit};
    use snarkvm_utilities::UniformRand;

    use rand::{
        distributions::{Distribution, Standard},
        thread_rng,
    };

    const ITERATIONS: usize = 1;

    fn test_mul<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>(
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

            let expected = first.wrapping_mul(&second);

            let name = format!("Mul: a * b {}", i);
            let compute_candidate = || {
                let a = Signed::<E, I, U, SIZE>::new(mode_a, first);
                let b = Signed::<E, I, U, SIZE>::new(mode_b, second);
                a * b
            };
            check_operation::<E, I, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    fn test_mul_assign<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>(
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

            let expected = first.wrapping_mul(&second);

            let name = format!("MulAssign: a *= b {}", i);
            let compute_candidate = || {
                let mut a = Signed::<E, I, U, SIZE>::new(mode_a, first);
                let b = Signed::<E, I, U, SIZE>::new(mode_b, second);
                a *= b;
                a
            };
            check_operation::<E, I, U, SIZE>(&name, expected, &compute_candidate, circuit_properties);
        }
    }

    #[test]
    fn test_i8_mul_constant_constant() {
        test_mul::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((24, 0, 0, 0)));
        test_mul_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Constant, Some((24, 0, 0, 0)));
    }

    #[test]
    fn test_i8_mul_constant_public() {
        test_mul::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_mul_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i8_mul_constant_private() {
        test_mul::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_mul_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i8_mul_public_constant() {
        test_mul::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_mul_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i8_mul_public_public() {
        test_mul::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((16, 16, 1009, 1881)));
        test_mul_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Public, Some((16, 16, 1009, 1881)));
    }

    #[test]
    fn test_i8_mul_public_private() {
        test_mul::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((16, 8, 1017, 1881)));
        test_mul_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Public, Mode::Private, Some((16, 8, 1017, 1881)));
    }

    #[test]
    fn test_i8_mul_private_constant() {
        test_mul::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_mul_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i8_mul_private_public() {
        test_mul::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((16, 8, 1017, 1881)));
        test_mul_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Public, Some((16, 8, 1017, 1881)));
    }

    #[test]
    fn test_i8_mul_private_private() {
        test_mul::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((16, 0, 1025, 1881)));
        test_mul_assign::<Circuit, i8, u8, 8>(ITERATIONS, Mode::Private, Mode::Private, Some((16, 0, 1025, 1881)));
    }

    // Tests for i16

    #[test]
    fn test_i16_mul_constant_constant() {
        test_mul::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((48, 0, 0, 0)));
        test_mul_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Constant, Some((48, 0, 0, 0)));
    }

    #[test]
    fn test_i16_mul_constant_public() {
        test_mul::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_mul_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i16_mul_constant_private() {
        test_mul::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_mul_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i16_mul_public_constant() {
        test_mul::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_mul_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i16_mul_public_public() {
        test_mul::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((32, 32, 4065, 7601)));
        test_mul_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Public, Some((32, 32, 4065, 7601)));
    }

    #[test]
    fn test_i16_mul_public_private() {
        test_mul::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((32, 16, 4081, 7601)));
        test_mul_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Public, Mode::Private, Some((32, 16, 4081, 7601)));
    }

    #[test]
    fn test_i16_mul_private_constant() {
        test_mul::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_mul_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i16_mul_private_public() {
        test_mul::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((32, 16, 4081, 7601)));
        test_mul_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Public, Some((32, 16, 4081, 7601)));
    }

    #[test]
    fn test_i16_mul_private_private() {
        test_mul::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((32, 0, 4097, 7601)));
        test_mul_assign::<Circuit, i16, u16, 16>(ITERATIONS, Mode::Private, Mode::Private, Some((32, 0, 4097, 7601)));
    }

    // Tests for i32

    #[test]
    fn test_i32_mul_constant_constant() {
        test_mul::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((96, 0, 0, 0)));
        test_mul_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Constant, Some((96, 0, 0, 0)));
    }

    #[test]
    fn test_i32_mul_constant_public() {
        test_mul::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_mul_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i32_mul_constant_private() {
        test_mul::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_mul_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i32_mul_public_constant() {
        test_mul::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_mul_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i32_mul_public_public() {
        test_mul::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((64, 64, 16321, 30561)));
        test_mul_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Public, Some((64, 64, 16321, 30561)));
    }

    #[test]
    fn test_i32_mul_public_private() {
        test_mul::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((64, 32, 16353, 30561)));
        test_mul_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Public, Mode::Private, Some((64, 32, 16353, 30561)));
    }

    #[test]
    fn test_i32_mul_private_constant() {
        test_mul::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_mul_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i32_mul_private_public() {
        test_mul::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((64, 32, 16353, 30561)));
        test_mul_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Public, Some((64, 32, 16353, 30561)));
    }

    #[test]
    fn test_i32_mul_private_private() {
        test_mul::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((64, 0, 16385, 30561)));
        test_mul_assign::<Circuit, i32, u32, 32>(ITERATIONS, Mode::Private, Mode::Private, Some((64, 0, 16385, 30561)));
    }

    // Tests for i64

    #[test]
    fn test_i64_mul_constant_constant() {
        test_mul::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((192, 0, 0, 0)));
        test_mul_assign::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Constant, Some((192, 0, 0, 0)));
    }

    #[test]
    fn test_i64_mul_constant_public() {
        test_mul::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_mul_assign::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i64_mul_constant_private() {
        test_mul::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_mul_assign::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i64_mul_public_constant() {
        test_mul::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_mul_assign::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i64_mul_public_public() {
        test_mul::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Public, Some((128, 128, 65409, 122561)));
        test_mul_assign::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Public,
            Mode::Public,
            Some((128, 128, 65409, 122561)),
        );
    }

    #[test]
    fn test_i64_mul_public_private() {
        test_mul::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Public, Mode::Private, Some((128, 64, 65473, 122561)));
        test_mul_assign::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Public,
            Mode::Private,
            Some((128, 64, 65473, 122561)),
        );
    }

    #[test]
    fn test_i64_mul_private_constant() {
        test_mul::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_mul_assign::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i64_mul_private_public() {
        test_mul::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Public, Some((128, 64, 65473, 122561)));
        test_mul_assign::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Private,
            Mode::Public,
            Some((128, 64, 65473, 122561)),
        );
    }

    #[test]
    fn test_i64_mul_private_private() {
        test_mul::<Circuit, i64, u64, 64>(ITERATIONS, Mode::Private, Mode::Private, Some((128, 0, 65537, 122561)));
        test_mul_assign::<Circuit, i64, u64, 64>(
            ITERATIONS,
            Mode::Private,
            Mode::Private,
            Some((128, 0, 65537, 122561)),
        );
    }

    // Tests for i128

    #[test]
    fn test_i128_mul_constant_constant() {
        test_mul::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((384, 0, 0, 0)));
        test_mul_assign::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Constant, Some((384, 0, 0, 0)));
    }

    #[test]
    fn test_i128_mul_constant_public() {
        test_mul::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
        test_mul_assign::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Public, None);
    }

    #[test]
    fn test_i128_mul_constant_private() {
        test_mul::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
        test_mul_assign::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Constant, Mode::Private, None);
    }

    #[test]
    fn test_i128_mul_public_constant() {
        test_mul::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
        test_mul_assign::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Constant, None);
    }

    #[test]
    fn test_i128_mul_public_public() {
        test_mul::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Public, Mode::Public, Some((256, 256, 261889, 490881)));
        test_mul_assign::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Public,
            Mode::Public,
            Some((256, 256, 261889, 490881)),
        );
    }

    #[test]
    fn test_i128_mul_public_private() {
        test_mul::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Public,
            Mode::Private,
            Some((256, 128, 262017, 490881)),
        );
        test_mul_assign::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Public,
            Mode::Private,
            Some((256, 128, 262017, 490881)),
        );
    }

    #[test]
    fn test_i128_mul_private_constant() {
        test_mul::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
        test_mul_assign::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Constant, None);
    }

    #[test]
    fn test_i128_mul_private_public() {
        test_mul::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Private,
            Mode::Public,
            Some((256, 128, 262017, 490881)),
        );
        test_mul_assign::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Private,
            Mode::Public,
            Some((256, 128, 262017, 490881)),
        );
    }

    #[test]
    fn test_i128_mul_private_private() {
        test_mul::<Circuit, i128, u128, 128>(ITERATIONS, Mode::Private, Mode::Private, Some((256, 0, 262145, 490881)));
        test_mul_assign::<Circuit, i128, u128, 128>(
            ITERATIONS,
            Mode::Private,
            Mode::Private,
            Some((256, 0, 262145, 490881)),
        );
    }
}
