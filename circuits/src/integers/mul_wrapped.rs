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

impl<E: Environment, I: IntegerType> MulWrapped<Self> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn mul_wrapped(&self, other: &Integer<E, I>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the product and return the new constant.
            Integer::new(Mode::Constant, self.eject_value().wrapping_mul(&other.eject_value()))
        } else {
            // Compute the product of `self` and `other`.
            let (product, _) = Self::mul_with_carry(&self, &other, false);
            // Return the product of `self` and `other`.
            product
        }
    }
}

impl<E: Environment, I: IntegerType> Integer<E, I> {
    /// Multiply the integer bits of `this` and `that` in the base field.
    #[inline]
    pub(super) fn mul_with_carry(
        this: &Integer<E, I>,
        that: &Integer<E, I>,
        include_carry_bits: bool,
    ) -> (Integer<E, I>, Vec<Boolean<E>>) {
        if 2 * I::BITS < E::BaseField::size_in_bits() - 1 {
            // Instead of multiplying the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and multiplied, before being converted back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let this = BaseField::from_bits_le(Mode::Private, &this.bits_le);
            let that = BaseField::from_bits_le(Mode::Private, &that.bits_le);
            let product = (this * that).to_lower_bits_le(2 * I::BITS);

            // Split the integer bits into product bits and carry bits.
            let (bits_le, carry) = product.split_at(I::BITS);

            // Return the product of `self` and `other`, along with the carry bits.
            (Integer::from_bits_le(Mode::Private, bits_le), carry.to_vec())
        } else if (I::BITS + I::BITS / 2) < E::BaseField::size_in_bits() - 1 {
            // Perform multiplication by decomposing it into operations on its upper and lower bits.
            // See this page for reference: https://en.wikipedia.org/wiki/Karatsuba_algorithm.
            // Note: We follow the naming convention given in the `Basic Step` section of the cited page.
            let x_1 = BaseField::from_bits_le(Mode::Private, &this.bits_le[(I::BITS / 2)..]);
            let x_0 = BaseField::from_bits_le(Mode::Private, &this.bits_le[..(I::BITS / 2)]);
            let y_1 = BaseField::from_bits_le(Mode::Private, &that.bits_le[(I::BITS / 2)..]);
            let y_0 = BaseField::from_bits_le(Mode::Private, &that.bits_le[..(I::BITS / 2)]);

            let z_0 = &x_0 * &y_0;
            let z_1 = (&x_1 * &y_0) + (&x_0 * &y_1);

            let mut b_m_bits = vec![Boolean::new(Mode::Constant, false); I::BITS / 2];
            b_m_bits.push(Boolean::new(Mode::Constant, true));

            let b_m = BaseField::from_bits_le(Mode::Constant, &b_m_bits);
            let z_0_plus_z_1 = &z_0 + (&z_1 * &b_m);

            let mut bits_le = z_0_plus_z_1.to_lower_bits_le(I::BITS + I::BITS / 2 + 1);

            match include_carry_bits {
                // Only `mul_checked` requires these bits to perform overflow/underflow checks.
                true => {
                    let z_2 = &x_1 * &y_1;
                    bits_le.append(&mut z_2.to_lower_bits_le(I::BITS));

                    // Split the integer bits into product bits and carry bits.
                    let (bits_le, carry) = bits_le.split_at(I::BITS);

                    // Return the product of `self` and `other`, along with the carry bits.
                    (Integer::from_bits_le(Mode::Private, bits_le), carry.to_vec())
                }
                false => {
                    // Remove any carry bits.
                    bits_le.truncate(I::BITS);

                    // Return the product of `self` and `other`, without the carry bits.
                    (Integer { bits_le, phantom: Default::default() }, vec![])
                }
            }
        } else {
            // TODO (@pranav) Do we need to handle this case? The current integers can
            //   be handled by the code above.
            todo!()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;
    use test_utilities::*;

    use rand::thread_rng;
    use std::ops::RangeInclusive;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_mul<I: IntegerType>(
        name: &str,
        first: I,
        second: I,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, I>::new(mode_b, second);
        let case = format!("({} * {})", a.eject_value(), b.eject_value());
        let expected = first.wrapping_mul(&second);
        check_operation_passes(name, &case, expected, &a, &b, Integer::mul_wrapped, num_constants, num_public, num_private, num_constraints);
        // Commute the operation.
        let a = Integer::<Circuit, I>::new(mode_a, second);
        let b = Integer::<Circuit, I>::new(mode_b, first);
        check_operation_passes(name, &case, expected, &a, &b, Integer::mul_wrapped, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let check_mul = | name: &str, first: I, second: I | check_mul(name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        for i in 0..ITERATIONS {
            // TODO (@pranav) Uniform random sampling almost always produces arguments that result in an overflow.
            //  Is there a better method for sampling arguments?
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: I = UniformRand::rand(&mut thread_rng());

            let name = format!("Mul: {} * {} {}", mode_a, mode_b, i);
            check_mul(&name, first, second);

            let name = format!("Double: {} * {} {}", mode_a, mode_b, i);
            check_mul(&name, first, I::one() + I::one());

            let name = format!("Square: {} * {} {}", mode_a, mode_a, i);
            check_mul(&name, first, first);
        }

        // Check specific cases common to signed and unsigned integers.
        check_mul("1 * MAX", I::one(), I::MAX);
        check_mul("MAX * 1", I::MAX, I::one());
        check_mul("1 * MIN",I::one(), I::MIN);
        check_mul("MIN * 1",I::MIN, I::one());
        check_mul("0 * MAX", I::zero(), I::MAX);
        check_mul( "MAX * 0", I::MAX, I::zero());
        check_mul( "0 * MIN", I::zero(), I::MIN);
        check_mul( "MIN * 0", I::MIN, I::zero());
        check_mul("1 * 1", I::one(), I::one());

        // Check common overflow cases.
        check_mul("MAX * 2", I::MAX, I::one() + I::one());
        check_mul("2 * MAX", I::one() + I::one(), I::MAX);

        // Check additional corner cases for signed integers.
        if I::is_signed() {
            check_mul("MAX * -1", I::MAX, I::zero() - I::one());
            check_mul("-1 * MAX", I::zero() - I::one(), I::MAX);

            check_mul("MIN * -1", I::MIN, I::zero() - I::one());
            check_mul("-1 * MIN", I::zero() - I::one(), I::MIN);
            check_mul("MIN * -2", I::MIN, I::zero() - I::one() - I::one());
            check_mul("-2 * MIN", I::zero() - I::one() - I::one(), I::MIN);
        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test<I: IntegerType>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        RangeInclusive<I>: Iterator<Item = I>
    {
        for first in I::MIN..=I::MAX {
            for second in I::MIN..=I::MAX {
                let name = format!("Mul: ({} * {})", first, second);
                check_mul(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            }
        }
    }

    #[test]
    fn test_u8_constant_times_constant() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_times_public() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_u8_constant_times_private() {
        type I = u8;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    fn test_u8_public_times_constant() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    fn test_u8_private_times_constant() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    fn test_u8_public_times_public() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_u8_public_times_private() {
        type I = u8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    fn test_u8_private_times_public() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_u8_private_times_private() {
        type I = u8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 19, 20);
    }

    // Tests for i8

    #[test]
    fn test_i8_constant_times_constant() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_times_public() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_i8_constant_times_private() {
        type I = i8;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    fn test_i8_public_times_constant() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    fn test_i8_private_times_constant() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    fn test_i8_public_times_public() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_i8_public_times_private() {
        type I = i8;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    fn test_i8_private_times_public() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    fn test_i8_private_times_private() {
        type I = i8;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 19, 20);
    }

    // Tests for u16

    #[test]
    fn test_u16_constant_times_constant() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_times_public() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_u16_constant_times_private() {
        type I = u16;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 35, 36);
    }

    #[test]
    fn test_u16_public_times_constant() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 35, 36);
    }

    #[test]
    fn test_u16_private_times_constant() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 35, 36);
    }

    #[test]
    fn test_u16_public_times_public() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_u16_public_times_private() {
        type I = u16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 35, 36);
    }

    #[test]
    fn test_u16_private_times_public() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_u16_private_times_private() {
        type I = u16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 35, 36);
    }

    // Tests for i16

    #[test]
    fn test_i16_constant_times_constant() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_times_public() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_i16_constant_times_private() {
        type I = i16;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 35, 36);
    }

    #[test]
    fn test_i16_public_times_constant() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 35, 36);
    }

    #[test]
    fn test_i16_private_times_constant() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 35, 36);
    }

    #[test]
    fn test_i16_public_times_public() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_i16_public_times_private() {
        type I = i16;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 35, 36);
    }

    #[test]
    fn test_i16_private_times_public() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 35, 36);
    }

    #[test]
    fn test_i16_private_times_private() {
        type I = i16;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 35, 36);
    }

    // Tests for u32

    #[test]
    fn test_u32_constant_times_constant() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_times_public() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_u32_constant_times_private() {
        type I = u32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 67, 68);
    }

    #[test]
    fn test_u32_public_times_constant() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 67, 68);
    }

    #[test]
    fn test_u32_private_times_constant() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 67, 68);
    }

    #[test]
    fn test_u32_public_times_public() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_u32_public_times_private() {
        type I = u32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 67, 68);
    }

    #[test]
    fn test_u32_private_times_public() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_u32_private_times_private() {
        type I = u32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 67, 68);
    }

    // Tests for i32

    #[test]
    fn test_i32_constant_times_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_times_public() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_i32_constant_times_private() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 67, 68);
    }

    #[test]
    fn test_i32_public_times_constant() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 67, 68);
    }

    #[test]
    fn test_i32_private_times_constant() {
        type I = i32;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 67, 68);
    }

    #[test]
    fn test_i32_public_times_public() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_i32_public_times_private() {
        type I = i32;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 67, 68);
    }

    #[test]
    fn test_i32_private_times_public() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 67, 68);
    }

    #[test]
    fn test_i32_private_times_private() {
        type I = i32;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 67, 68);
    }

    // Tests for u64

    #[test]
    fn test_u64_constant_times_constant() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_times_public() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_u64_constant_times_private() {
        type I = u64;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 131, 132);
    }

    #[test]
    fn test_u64_public_times_constant() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 131, 132);
    }

    #[test]
    fn test_u64_private_times_constant() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 131, 132);
    }

    #[test]
    fn test_u64_public_times_public() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_u64_public_times_private() {
        type I = u64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 131, 132);
    }

    #[test]
    fn test_u64_private_times_public() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_u64_private_times_private() {
        type I = u64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 131, 132);
    }

    // Tests for i64

    #[test]
    fn test_i64_constant_times_constant() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_times_public() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_i64_constant_times_private() {
        type I = i64;
        run_test::<I>(Mode::Constant, Mode::Private, 2, 0, 131, 132);
    }

    #[test]
    fn test_i64_public_times_constant() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Constant, 2, 0, 131, 132);
    }

    #[test]
    fn test_i64_private_times_constant() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Constant, 2, 0, 131, 132);
    }

    #[test]
    fn test_i64_public_times_public() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_i64_public_times_private() {
        type I = i64;
        run_test::<I>(Mode::Public, Mode::Private, 2, 0, 131, 132);
    }

    #[test]
    fn test_i64_private_times_public() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Public, 2, 0, 131, 132);
    }

    #[test]
    fn test_i64_private_times_private() {
        type I = i64;
        run_test::<I>(Mode::Private, Mode::Private, 2, 0, 131, 132);
    }

    // Tests for u128

    #[test]
    fn test_u128_constant_times_constant() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_times_public() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Public, 8, 0, 200, 201);
    }

    #[test]
    fn test_u128_constant_times_private() {
        type I = u128;
        run_test::<I>(Mode::Constant, Mode::Private, 8, 0, 200, 201);
    }

    #[test]
    fn test_u128_public_times_constant() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Constant, 8, 0, 200, 201);
    }

    #[test]
    fn test_u128_private_times_constant() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Constant, 8, 0, 200, 201);
    }

    #[test]
    fn test_u128_public_times_public() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Public, 8, 0, 200, 201);
    }

    #[test]
    fn test_u128_public_times_private() {
        type I = u128;
        run_test::<I>(Mode::Public, Mode::Private, 8, 0, 200, 201);
    }

    #[test]
    fn test_u128_private_times_public() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Public, 8, 0, 200, 201);
    }

    #[test]
    fn test_u128_private_times_private() {
        type I = u128;
        run_test::<I>(Mode::Private, Mode::Private, 8, 0, 200, 201);
    }

    // Tests for i128

    #[test]
    fn test_i128_constant_times_constant() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_times_public() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Public, 8, 0, 200, 201);
    }

    #[test]
    fn test_i128_constant_times_private() {
        type I = i128;
        run_test::<I>(Mode::Constant, Mode::Private, 8, 0, 200, 201);
    }

    #[test]
    fn test_i128_public_times_constant() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Constant, 8, 0, 200, 201);
    }

    #[test]
    fn test_i128_private_times_constant() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Constant, 8, 0, 200, 201);
    }

    #[test]
    fn test_i128_public_times_public() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Public, 8, 0, 200, 201);
    }

    #[test]
    fn test_i128_public_times_private() {
        type I = i128;
        run_test::<I>(Mode::Public, Mode::Private, 8, 0, 200, 201);
    }

    #[test]
    fn test_i128_private_times_public() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Public, 8, 0, 200, 201);
    }

    #[test]
    fn test_i128_private_times_private() {
        type I = i128;
        run_test::<I>(Mode::Private, Mode::Private, 8, 0, 200, 201);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_times_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_times_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_times_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_times_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_times_constant() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_times_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_times_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_times_public() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_times_private() {
        type I = u8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 2, 0, 19, 20);
    }

    // Exhaustive tests for i8.

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_times_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_times_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_times_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Constant, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_times_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_times_constant() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Constant, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_times_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_times_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Public, Mode::Private, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_times_public() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Public, 2, 0, 19, 20);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_times_private() {
        type I = i8;
        run_exhaustive_test::<I>(Mode::Private, Mode::Private, 2, 0, 19, 20);
    }
}
