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

impl<E: Environment, I: IntegerType, M: Magnitude> ShrWrapped<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn shr_wrapped(&self, rhs: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && rhs.is_constant() {
            // This cast is safe since `Magnitude`s can only be `u8`, `u16`, or `u32`.
            Integer::new(Mode::Constant, self.eject_value().wrapping_shr(rhs.eject_value().to_u32().unwrap()))
        } else {
            // Index of the first upper bit of rhs that we mask.
            let first_upper_bit_index = I::BITS.trailing_zeros() as usize;

            // Perform the right shift operation by exponentiation and multiplication.
            // By masking the upper bits, we have that rhs < I::BITS.
            // Therefore, 2^{rhs} < I::MAX.
            let mut lower_rhs_bits = Vec::with_capacity(8);
            lower_rhs_bits.extend_from_slice(&rhs.bits_le[..first_upper_bit_index]);
            lower_rhs_bits.resize(8, Boolean::constant(false));

            // Use U8 for the exponent as it costs fewer constraints.
            let rhs_as_u8 = U8 { bits_le: lower_rhs_bits, phantom: Default::default() };

            if rhs_as_u8.is_constant() {
                // If the shift amount is a constant, then we can manually shift in bits and truncate the result.
                let shift_amount = rhs_as_u8.eject_value() as usize;

                let mut bits_le = Vec::with_capacity(I::BITS + shift_amount);
                bits_le.extend_from_slice(&self.bits_le);

                match I::is_signed() {
                    // Sign-extend `self` by `shift_amount`.
                    true => bits_le.extend(core::iter::repeat(self.msb().clone()).take(shift_amount)),
                    // Zero-extend `self` by `shift_amount`.
                    false => bits_le.extend(core::iter::repeat(Boolean::constant(false)).take(shift_amount)),
                };

                bits_le.reverse();
                bits_le.truncate(I::BITS);
                bits_le.reverse();

                Self { bits_le, phantom: Default::default() }
            } else {
                // Calculate the value of the shift directly in the field.
                // Since 2^{rhs} < I::MAX, we know that the operation will not overflow I::MAX or the field modulus.
                let two = Field::one() + Field::one();
                let mut shift_in_field = Field::one();
                for bit in rhs.bits_le[..first_upper_bit_index].iter().rev() {
                    shift_in_field = shift_in_field.square();
                    shift_in_field = Field::ternary(bit, &(&shift_in_field * &two), &shift_in_field);
                }

                // TODO (@pranav) Avoid initializing the integer.
                let shift_as_divisor =
                    Self { bits_le: shift_in_field.to_lower_bits_le(I::BITS), phantom: Default::default() };

                if I::is_signed() {
                    // Divide the absolute value of `self` and `shift` (as a divisor) in the base field.
                    let dividend_unsigned = self.abs_wrapped().cast_as_dual();
                    let divisor_unsigned = shift_as_divisor.cast_as_dual();

                    let dividend = dividend_unsigned.eject_value();
                    let divisor = divisor_unsigned.eject_value();

                    // Wrapping operations are safe since unsigned division never overflows.
                    let quotient_unsigned = Integer::<E, I::Dual>::new(Mode::Private, dividend.wrapping_div(&divisor));
                    let remainder_unsigned = Integer::<E, I::Dual>::new(Mode::Private, dividend.wrapping_rem(&divisor));

                    // Ensure that Euclidean division holds for these values in the base field.
                    let remainder_field = remainder_unsigned.to_field();
                    E::assert_eq(
                        dividend_unsigned.to_field(),
                        quotient_unsigned.to_field() * divisor_unsigned.to_field() + &remainder_field,
                    );

                    // TODO (@pranav) Do we need to check that the quotient cannot exceed abs(I::MIN)?
                    //  This is implicitly true since the dividend <= abs(I::MIN) and 0 <= quotient <= dividend.
                    let quotient = Self { bits_le: quotient_unsigned.bits_le, phantom: Default::default() };
                    let negated_quotient = &(!&quotient).add_wrapped(&Self::one());

                    // Arithmetic shift uses a different rounding mode than division.
                    let rounded_negated_quotient = Self::ternary(
                        &remainder_field.is_equal(&Field::zero()),
                        negated_quotient,
                        &(negated_quotient).sub_wrapped(&Self::one()),
                    );

                    Self::ternary(self.msb(), &rounded_negated_quotient, &quotient)
                } else {
                    self.div_wrapped(&shift_as_divisor)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};
    use test_utilities::*;

    use std::{ops::RangeInclusive, panic::RefUnwindSafe};

    const ITERATIONS: usize = 32;

    #[rustfmt::skip]
    fn check_shr<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        name: &str,
        first: I,
        second: M,
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let expected = first.wrapping_shr(second.to_u32().unwrap());
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        let case = format!("({} >> {})", a.eject_value(), b.eject_value());

        check_operation_passes(name, &case, expected, &a, &b, Integer::shr_wrapped, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let check_shr = | name: &str, first: I, second: M | check_shr(name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut test_rng());
            let second: M = UniformRand::rand(&mut test_rng());

            let name = format!("Shr: {} >> {} {}", mode_a, mode_b, i);
            check_shr(&name, first, second);

            // Check that shift right by one is computed correctly.
            let name = format!("Half: {} >> {} {}", mode_a, mode_b, i);
            check_shr(&name, first, M::one());
        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test<I: IntegerType + RefUnwindSafe, M: Magnitude + RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        RangeInclusive<I>: Iterator<Item = I>,
        RangeInclusive<M>: Iterator<Item = M>
    {
        for first in I::MIN..=I::MAX {
            for second in M::MIN..=M::MAX {
                let name = format!("Shr: ({} >> {})", first, second);
                check_shr(&name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);
            }
        }
    }

    // Tests for u8, where shift magnitude is u8

    #[test]
    fn test_u8_constant_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_constant_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_public_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_public_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_private_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_private_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 29, 31);
    }

    // Tests for i8, where shift magnitude is u8

    #[test]
    fn test_i8_constant_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 32, 0, 57, 62);
    }

    #[test]
    fn test_i8_constant_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 32, 0, 57, 62);
    }

    #[test]
    fn test_i8_public_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 24, 0, 82, 88);
    }

    #[test]
    fn test_i8_public_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 24, 0, 82, 88);
    }

    #[test]
    fn test_i8_private_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 24, 0, 82, 88);
    }

    #[test]
    fn test_i8_private_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 24, 0, 82, 88);
    }

    // Tests for u16, where shift magnitude is u8

    #[test]
    fn test_u16_constant_shr_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shr_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_constant_shr_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_public_shr_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_shr_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shr_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_public_shr_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_private_shr_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_private_shr_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 55, 57);
    }

    // Tests for i16, where shift magnitude is u8

    #[test]
    fn test_i16_constant_shr_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shr_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 64, 0, 107, 112);
    }

    #[test]
    fn test_i16_constant_shr_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 64, 0, 107, 112);
    }

    #[test]
    fn test_i16_public_shr_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_shr_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shr_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 48, 0, 156, 162);
    }

    #[test]
    fn test_i16_public_shr_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 48, 0, 156, 162);
    }

    #[test]
    fn test_i16_private_shr_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 48, 0, 156, 162);
    }

    #[test]
    fn test_i16_private_shr_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 48, 0, 156, 162);
    }

    // Tests for u32, where shift magnitude is u8

    #[test]
    fn test_u32_constant_shr_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shr_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_constant_shr_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_public_shr_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_shr_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shr_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_public_shr_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_private_shr_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_private_shr_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 105, 107);
    }

    // Tests for i32, where shift magnitude is u8

    #[test]
    fn test_i32_constant_shr_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shr_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 128, 0, 205, 210);
    }

    #[test]
    fn test_i32_constant_shr_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 128, 0, 205, 210);
    }

    #[test]
    fn test_i32_public_shr_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_shr_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shr_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 96, 0, 302, 308);
    }

    #[test]
    fn test_i32_public_shr_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 96, 0, 302, 308);
    }

    #[test]
    fn test_i32_private_shr_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 96, 0, 302, 308);
    }

    #[test]
    fn test_i32_private_shr_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 96, 0, 302, 308);
    }

    // Tests for u64, where shift magnitude is u8

    #[test]
    fn test_u64_constant_shr_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shr_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_constant_shr_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_public_shr_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_shr_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shr_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_public_shr_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_private_shr_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_private_shr_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 203, 205);
    }

    // Tests for i64, where shift magnitude is u8

    #[test]
    fn test_i64_constant_shr_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shr_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 256, 0, 399, 404);
    }

    #[test]
    fn test_i64_constant_shr_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 256, 0, 399, 404);
    }

    #[test]
    fn test_i64_public_shr_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_shr_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shr_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 192, 0, 592, 598);
    }

    #[test]
    fn test_i64_public_shr_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 192, 0, 592, 598);
    }

    #[test]
    fn test_i64_private_shr_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 192, 0, 592, 598);
    }

    #[test]
    fn test_i64_private_shr_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 192, 0, 592, 598);
    }

    // Tests for u128, where shift magnitude is u8

    #[test]
    fn test_u128_constant_shr_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shr_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_constant_shr_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_public_shr_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_shr_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shr_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_public_shr_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_private_shr_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_private_shr_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 397, 399);
    }

    // Tests for i128, where shift magnitude is u8

    #[test]
    fn test_i128_constant_shr_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shr_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 512, 0, 785, 790);
    }

    #[test]
    fn test_i128_constant_shr_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 512, 0, 785, 790);
    }

    #[test]
    fn test_i128_public_shr_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_shr_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shr_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 384, 0, 1170, 1176);
    }

    #[test]
    fn test_i128_public_shr_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 384, 0, 1170, 1176);
    }

    #[test]
    fn test_i128_private_shr_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 384, 0, 1170, 1176);
    }

    #[test]
    fn test_i128_private_shr_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 384, 0, 1170, 1176);
    }

    // Tests for u8, where shift magnitude is u16

    #[test]
    fn test_u8_constant_shr_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shr_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_constant_shr_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_public_shr_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_shr_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shr_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_public_shr_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_private_shr_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_private_shr_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 29, 31);
    }

    // Tests for i8, where shift magnitude is u16

    #[test]
    fn test_i8_constant_shr_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shr_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 32, 0, 57, 62);
    }

    #[test]
    fn test_i8_constant_shr_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 32, 0, 57, 62);
    }

    #[test]
    fn test_i8_public_shr_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_shr_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shr_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 24, 0, 82, 88);
    }

    #[test]
    fn test_i8_public_shr_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 24, 0, 82, 88);
    }

    #[test]
    fn test_i8_private_shr_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 24, 0, 82, 88);
    }

    #[test]
    fn test_i8_private_shr_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 24, 0, 82, 88);
    }

    // Tests for u16, where shift magnitude is u16

    #[test]
    fn test_u16_constant_shr_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shr_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_constant_shr_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_public_shr_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_shr_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shr_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_public_shr_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_private_shr_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_private_shr_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 55, 57);
    }

    // Tests for i16, where shift magnitude is u16

    #[test]
    fn test_i16_constant_shr_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shr_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 64, 0, 107, 112);
    }

    #[test]
    fn test_i16_constant_shr_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 64, 0, 107, 112);
    }

    #[test]
    fn test_i16_public_shr_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_shr_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shr_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 48, 0, 156, 162);
    }

    #[test]
    fn test_i16_public_shr_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 48, 0, 156, 162);
    }

    #[test]
    fn test_i16_private_shr_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 48, 0, 156, 162);
    }

    #[test]
    fn test_i16_private_shr_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 48, 0, 156, 162);
    }

    // Tests for u32, where shift magnitude is u16

    #[test]
    fn test_u32_constant_shr_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shr_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_constant_shr_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_public_shr_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_shr_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shr_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_public_shr_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_private_shr_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_private_shr_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 105, 107);
    }

    // Tests for i32, where shift magnitude is u16

    #[test]
    fn test_i32_constant_shr_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shr_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 128, 0, 205, 210);
    }

    #[test]
    fn test_i32_constant_shr_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 128, 0, 205, 210);
    }

    #[test]
    fn test_i32_public_shr_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_shr_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shr_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 96, 0, 302, 308);
    }

    #[test]
    fn test_i32_public_shr_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 96, 0, 302, 308);
    }

    #[test]
    fn test_i32_private_shr_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 96, 0, 302, 308);
    }

    #[test]
    fn test_i32_private_shr_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 96, 0, 302, 308);
    }

    // Tests for u64, where shift magnitude is u16

    #[test]
    fn test_u64_constant_shr_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shr_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_constant_shr_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_public_shr_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_shr_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shr_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_public_shr_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_private_shr_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_private_shr_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 203, 205);
    }

    // Tests for i64, where shift magnitude is u16

    #[test]
    fn test_i64_constant_shr_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shr_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 256, 0, 399, 404);
    }

    #[test]
    fn test_i64_constant_shr_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 256, 0, 399, 404);
    }

    #[test]
    fn test_i64_public_shr_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_shr_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shr_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 192, 0, 592, 598);
    }

    #[test]
    fn test_i64_public_shr_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 192, 0, 592, 598);
    }

    #[test]
    fn test_i64_private_shr_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 192, 0, 592, 598);
    }

    #[test]
    fn test_i64_private_shr_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 192, 0, 592, 598);
    }

    // Tests for u128, where shift magnitude is u16

    #[test]
    fn test_u128_constant_shr_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shr_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_constant_shr_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_public_shr_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_shr_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shr_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_public_shr_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_private_shr_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_private_shr_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 397, 399);
    }

    // Tests for i128, where shift magnitude is u16

    #[test]
    fn test_i128_constant_shr_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shr_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 512, 0, 785, 790);
    }

    #[test]
    fn test_i128_constant_shr_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 512, 0, 785, 790);
    }

    #[test]
    fn test_i128_public_shr_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_shr_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shr_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 384, 0, 1170, 1176);
    }

    #[test]
    fn test_i128_public_shr_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 384, 0, 1170, 1176);
    }

    #[test]
    fn test_i128_private_shr_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 384, 0, 1170, 1176);
    }

    #[test]
    fn test_i128_private_shr_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 384, 0, 1170, 1176);
    }

    // Tests for u8, where shift magnitude is u32

    #[test]
    fn test_u8_constant_shr_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shr_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_constant_shr_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_public_shr_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_shr_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shr_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_public_shr_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_private_shr_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    fn test_u8_private_shr_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 29, 31);
    }

    // Tests for i8, where shift magnitude is u32

    #[test]
    fn test_i8_constant_shr_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shr_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 32, 0, 57, 62);
    }

    #[test]
    fn test_i8_constant_shr_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 32, 0, 57, 62);
    }

    #[test]
    fn test_i8_public_shr_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_shr_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shr_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 24, 0, 82, 88);
    }

    #[test]
    fn test_i8_public_shr_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 24, 0, 82, 88);
    }

    #[test]
    fn test_i8_private_shr_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 24, 0, 82, 88);
    }

    #[test]
    fn test_i8_private_shr_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 24, 0, 82, 88);
    }

    // Tests for u16, where shift magnitude is u32

    #[test]
    fn test_u16_constant_shr_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shr_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_constant_shr_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_public_shr_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_shr_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shr_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_public_shr_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_private_shr_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 55, 57);
    }

    #[test]
    fn test_u16_private_shr_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 55, 57);
    }

    // Tests for i16, where shift magnitude is u32

    #[test]
    fn test_i16_constant_shr_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shr_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 64, 0, 107, 112);
    }

    #[test]
    fn test_i16_constant_shr_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 64, 0, 107, 112);
    }

    #[test]
    fn test_i16_public_shr_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_shr_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shr_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 48, 0, 156, 162);
    }

    #[test]
    fn test_i16_public_shr_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 48, 0, 156, 162);
    }

    #[test]
    fn test_i16_private_shr_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 48, 0, 156, 162);
    }

    #[test]
    fn test_i16_private_shr_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 48, 0, 156, 162);
    }

    // Tests for u32, where shift magnitude is u32

    #[test]
    fn test_u32_constant_shr_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shr_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_constant_shr_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_public_shr_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_shr_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shr_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_public_shr_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_private_shr_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 105, 107);
    }

    #[test]
    fn test_u32_private_shr_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 105, 107);
    }

    // Tests for i32, where shift magnitude is u32

    #[test]
    fn test_i32_constant_shr_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shr_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 128, 0, 205, 210);
    }

    #[test]
    fn test_i32_constant_shr_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 128, 0, 205, 210);
    }

    #[test]
    fn test_i32_public_shr_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_shr_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shr_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 96, 0, 302, 308);
    }

    #[test]
    fn test_i32_public_shr_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 96, 0, 302, 308);
    }

    #[test]
    fn test_i32_private_shr_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 96, 0, 302, 308);
    }

    #[test]
    fn test_i32_private_shr_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 96, 0, 302, 308);
    }

    // Tests for u64, where shift magnitude is u32

    #[test]
    fn test_u64_constant_shr_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shr_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_constant_shr_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_public_shr_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_shr_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shr_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_public_shr_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_private_shr_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 203, 205);
    }

    #[test]
    fn test_u64_private_shr_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 203, 205);
    }

    // Tests for i64, where shift magnitude is u32

    #[test]
    fn test_i64_constant_shr_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shr_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 256, 0, 399, 404);
    }

    #[test]
    fn test_i64_constant_shr_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 256, 0, 399, 404);
    }

    #[test]
    fn test_i64_public_shr_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_shr_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shr_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 192, 0, 592, 598);
    }

    #[test]
    fn test_i64_public_shr_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 192, 0, 592, 598);
    }

    #[test]
    fn test_i64_private_shr_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 192, 0, 592, 598);
    }

    #[test]
    fn test_i64_private_shr_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 192, 0, 592, 598);
    }

    // Tests for u128, where shift magnitude is u32

    #[test]
    fn test_u128_constant_shr_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shr_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_constant_shr_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_public_shr_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_shr_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shr_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_public_shr_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_private_shr_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 397, 399);
    }

    #[test]
    fn test_u128_private_shr_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 397, 399);
    }

    // Tests for i128, where shift magnitude is u32

    #[test]
    fn test_i128_constant_shr_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shr_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Public, 512, 0, 785, 790);
    }

    #[test]
    fn test_i128_constant_shr_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 512, 0, 785, 790);
    }

    #[test]
    fn test_i128_public_shr_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_shr_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shr_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 384, 0, 1170, 1176);
    }

    #[test]
    fn test_i128_public_shr_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 384, 0, 1170, 1176);
    }

    #[test]
    fn test_i128_private_shr_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 384, 0, 1170, 1176);
    }

    #[test]
    fn test_i128_private_shr_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 384, 0, 1170, 1176);
    }

    // Exhaustive tests for u8.

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Private, 0, 0, 29, 31);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 0, 0, 29, 31);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 0, 0, 29, 31);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 0, 0, 29, 31);
    }

    // Tests for i8, where shift magnitude is u8

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Public, 32, 0, 57, 62);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Constant, Mode::Private, 32, 0, 57, 62);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Constant, 0, 0, 0, 0);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 24, 0, 82, 88);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 24, 0, 82, 88);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 24, 0, 82, 88);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 24, 0, 82, 88);
    }
}
