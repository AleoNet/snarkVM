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
use crate::{SignExtend, ZeroExtend};

impl<E: Environment, I: IntegerType, M: private::Magnitude> ShrChecked<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn shr_checked(&self, rhs: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && rhs.is_constant() {
            // This cast is safe since `Magnitude`s can only be `u8`, `u16`, or `u32`.
            match self.eject_value().checked_shr(rhs.eject_value().to_u32().unwrap()) {
                Some(value) => Integer::new(Mode::Constant, value),
                None => E::halt("Constant shifted by constant exceeds the allowed bitwidth."),
            }
        } else {
            // Index of the first upper bit of rhs that must be zero.
            // This is a safe case as I::BITS = 8, 16, 32, or 128.
            // Therefore there is at least one trailing zero.
            let first_upper_bit_index = I::BITS.trailing_zeros() as usize;

            let upper_bits_are_nonzero = rhs.bits_le[first_upper_bit_index..]
                .iter()
                .fold(Boolean::new(Mode::Private, false), |at_least_one_is_set, bit| at_least_one_is_set.or(&bit));

            // The below constraint is not enforced if it is a constant.
            if upper_bits_are_nonzero.is_constant() {
                E::halt("Constant shifted by constant exceeds the allowed bitwidth.")
            }
            // Enforce that the appropriate number of upper bits in rhs are zero.
            E::assert_eq(upper_bits_are_nonzero, E::zero());

            // Perform the right shift operation by exponentiation and multiplication.
            // By enforcing that the upper bits are zero, we have that rhs < I::BITS.
            // Therefore, 2^{rhs} < I::MAX.
            let mut lower_rhs_bits = Vec::with_capacity(8);
            lower_rhs_bits.extend_from_slice(&rhs.bits_le[..first_upper_bit_index]);
            lower_rhs_bits.resize(8, Boolean::new(Mode::Constant, false));

            // Use U8 for the exponent as it costs fewer constraints.
            let rhs_as_u8 = U8::<E> { bits_le: lower_rhs_bits, phantom: Default::default() };

            if rhs_as_u8.is_constant() {
                // If the shift amount is a constant, then we can manually shift in bits and truncate the result.
                let shift_amount = rhs_as_u8.eject_value() as usize;
                let mut bits_le = if I::is_signed() {
                    Boolean::sign_extend(&self.bits_le, I::BITS + shift_amount)
                } else {
                    Boolean::zero_extend(&self.bits_le, I::BITS + shift_amount)
                };

                bits_le.reverse();
                bits_le.truncate(I::BITS);
                bits_le.reverse();

                Self { bits_le, phantom: Default::default() }
            } else {
                // Calculate the value of the shift directly in the field.
                // Since 2^{rhs} < I::MAX, we know that the operation will not overflow I::MAX or the field modulus.
                let two = BaseField::one() + BaseField::one();
                let mut shift_in_field = BaseField::one();
                for bit in rhs.bits_le[..first_upper_bit_index].into_iter().rev() {
                    shift_in_field = &shift_in_field * &shift_in_field;
                    shift_in_field = BaseField::ternary(bit, &(&shift_in_field * &two), &shift_in_field);
                }

                // TODO (@pranav) Avoid initializing the integer.
                let shift_as_divisor =
                    Self { bits_le: shift_in_field.to_lower_bits_le(I::BITS), phantom: Default::default() };

                if I::is_signed() {
                    // This is safe as I::BITS is always greater than zero.
                    let self_is_negative = self.bits_le.last().unwrap();

                    // Divide the absolute value of `self` and `shift` (as a divisor) in the base field.
                    let dividend_unsigned_integer =
                        Self::ternary(self_is_negative, &(!self).add_wrapped(&Self::one()), self).cast_as_dual();
                    let divisor_unsigned_integer = shift_as_divisor.cast_as_dual();

                    let dividend_unsigned_value = dividend_unsigned_integer.eject_value();
                    let divisor_unsigned_value = divisor_unsigned_integer.eject_value();

                    // Wrapping operations are safe since unsigned division never overflows.
                    let quotient_unsigned_value = dividend_unsigned_value.wrapping_div(&divisor_unsigned_value);
                    let remainder_unsigned_value = dividend_unsigned_value.wrapping_rem(&divisor_unsigned_value);

                    let quotient_unsigned_integer = Integer::<E, I::Dual>::new(Mode::Private, quotient_unsigned_value);
                    let remainder_unsigned_integer =
                        Integer::<E, I::Dual>::new(Mode::Private, remainder_unsigned_value);

                    let dividend_field = BaseField::from_bits_le(Mode::Private, &dividend_unsigned_integer.bits_le);
                    let divisor_field = BaseField::from_bits_le(Mode::Private, &divisor_unsigned_integer.bits_le);
                    let quotient_field = BaseField::from_bits_le(Mode::Private, &quotient_unsigned_integer.bits_le);
                    let remainder_field = BaseField::from_bits_le(Mode::Private, &remainder_unsigned_integer.bits_le);

                    E::assert_eq(dividend_field, quotient_field * divisor_field + &remainder_field);

                    // TODO (@pranav) Do we need to check that the quotient cannot exceed abs(I::MIN)?
                    //  This is implicitly true since the dividend <= abs(I::MIN) and 0 <= quotient <= dividend.
                    let quotient_integer =
                        Self { bits_le: quotient_unsigned_integer.bits_le, phantom: Default::default() };
                    let negated_quotient = &(!&quotient_integer).add_wrapped(&Self::one());

                    // Arithmetic shift uses a different rounding mode than division.
                    let rounded_negated_quotient = Self::ternary(
                        &(&remainder_field).is_eq(&BaseField::zero()),
                        &negated_quotient,
                        &(&negated_quotient).sub_wrapped(&Self::one()),
                    );

                    Self::ternary(&self_is_negative, &rounded_negated_quotient, &quotient_integer)
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
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;
    use test_utilities::*;

    use rand::thread_rng;
    use std::ops::Range;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_shr<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
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
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        let case = format!("({} >> {})", a.eject_value(), b.eject_value());

        // Pass in the appropriate expected numbers based on the mode.
        let (num_constants, num_public, num_private, num_constraints) = match (mode_a, mode_b) {
            (Mode::Public, Mode::Constant) => (2, 0, 1, 2),
            (Mode::Private, Mode::Constant) => (2, 0, 1, 2),
            _ =>  (num_constants, num_public, num_private, num_constraints),
        };

        match first.checked_shr(second.to_u32().unwrap()) {
            Some(value) => {
                check_binary_operation_passes(name,  &case,value, &a, &b, Integer::shr_checked, num_constants, num_public, num_private, num_constraints);
            }
            None => match (mode_a, mode_b) {
                (_, Mode::Constant) => check_binary_operation_halts(&a, &b, Integer::shr_checked),
                _ => check_binary_operation_fails(name, &case, &a, &b, Integer::shr_checked, num_constants, num_public, num_private, num_constraints),
            },
        };
    }

    #[rustfmt::skip]
    fn run_test<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let check_shr = | name: &str, first: I, second: M | check_shr(name, first, second, mode_a, mode_b, num_constants, num_public, num_private, num_constraints);

        for i in 0..ITERATIONS {
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: M = UniformRand::rand(&mut thread_rng());

            let name = format!("Shr: {} >> {} {}", mode_a, mode_b, i);
            check_shr(&name, first, second);

            // Check that shift right by one is computed correctly.
            let name = format!("Half: {} >> {} {}", mode_a, mode_b, i);
            check_shr(&name, first, M::one());
        }
    }

    #[rustfmt::skip]
    fn run_exhaustive_test<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) where
        Range<I>: Iterator<Item = I>,
        Range<M>: Iterator<Item = M>
    {
        for first in I::MIN..I::MAX {
            for second in M::MIN..M::MAX {
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 37, 40);
    }

    #[test]
    fn test_u8_constant_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 37, 40);
    }

    #[test]
    fn test_u8_public_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 37, 40);
    }

    #[test]
    fn test_u8_private_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 37, 40);
    }

    #[test]
    fn test_u8_public_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 37, 40);
    }

    #[test]
    fn test_u8_public_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 37, 40);
    }

    #[test]
    fn test_u8_private_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 37, 40);
    }

    #[test]
    fn test_u8_private_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 37, 40);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 37, 40);
    }

    #[test]
    fn test_i8_constant_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 37, 40);
    }

    #[test]
    fn test_i8_public_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 37, 40);
    }

    #[test]
    fn test_i8_private_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 37, 40);
    }

    #[test]
    fn test_i8_public_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 37, 40);
    }

    #[test]
    fn test_i8_public_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 37, 40);
    }

    #[test]
    fn test_i8_private_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 37, 40);
    }

    #[test]
    fn test_i8_private_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 37, 40);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 62, 65);
    }

    #[test]
    fn test_u16_constant_shr_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 62, 65);
    }

    #[test]
    fn test_u16_public_shr_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 62, 65);
    }

    #[test]
    fn test_u16_private_shr_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 62, 65);
    }

    #[test]
    fn test_u16_public_shr_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 62, 65);
    }

    #[test]
    fn test_u16_public_shr_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 62, 65);
    }

    #[test]
    fn test_u16_private_shr_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 62, 65);
    }

    #[test]
    fn test_u16_private_shr_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 62, 65);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 62, 65);
    }

    #[test]
    fn test_i16_constant_shr_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 62, 65);
    }

    #[test]
    fn test_i16_public_shr_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 62, 65);
    }

    #[test]
    fn test_i16_private_shr_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 62, 65);
    }

    #[test]
    fn test_i16_public_shr_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 62, 65);
    }

    #[test]
    fn test_i16_public_shr_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 62, 65);
    }

    #[test]
    fn test_i16_private_shr_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 62, 65);
    }

    #[test]
    fn test_i16_private_shr_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 62, 65);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 111, 114);
    }

    #[test]
    fn test_u32_constant_shr_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 111, 114);
    }

    #[test]
    fn test_u32_public_shr_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 111, 114);
    }

    #[test]
    fn test_u32_private_shr_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 111, 114);
    }

    #[test]
    fn test_u32_public_shr_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 111, 114);
    }

    #[test]
    fn test_u32_public_shr_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 111, 114);
    }

    #[test]
    fn test_u32_private_shr_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 111, 114);
    }

    #[test]
    fn test_u32_private_shr_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 111, 114);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 111, 114);
    }

    #[test]
    fn test_i32_constant_shr_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 111, 114);
    }

    #[test]
    fn test_i32_public_shr_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 111, 114);
    }

    #[test]
    fn test_i32_private_shr_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 111, 114);
    }

    #[test]
    fn test_i32_public_shr_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 111, 114);
    }

    #[test]
    fn test_i32_public_shr_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 111, 114);
    }

    #[test]
    fn test_i32_private_shr_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 111, 114);
    }

    #[test]
    fn test_i32_private_shr_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 111, 114);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 208, 211);
    }

    #[test]
    fn test_u64_constant_shr_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 208, 211);
    }

    #[test]
    fn test_u64_public_shr_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 208, 211);
    }

    #[test]
    fn test_u64_private_shr_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 208, 211);
    }

    #[test]
    fn test_u64_public_shr_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 208, 211);
    }

    #[test]
    fn test_u64_public_shr_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 208, 211);
    }

    #[test]
    fn test_u64_private_shr_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 208, 211);
    }

    #[test]
    fn test_u64_private_shr_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 208, 211);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 208, 211);
    }

    #[test]
    fn test_i64_constant_shr_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 208, 211);
    }

    #[test]
    fn test_i64_public_shr_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 208, 211);
    }

    #[test]
    fn test_i64_private_shr_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 208, 211);
    }

    #[test]
    fn test_i64_public_shr_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 208, 211);
    }

    #[test]
    fn test_i64_public_shr_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 208, 211);
    }

    #[test]
    fn test_i64_private_shr_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 208, 211);
    }

    #[test]
    fn test_i64_private_shr_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 208, 211);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 9, 0, 342, 345);
    }

    #[test]
    fn test_u128_constant_shr_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 9, 0, 342, 345);
    }

    #[test]
    fn test_u128_public_shr_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 9, 0, 342, 345);
    }

    #[test]
    fn test_u128_private_shr_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 9, 0, 342, 345);
    }

    #[test]
    fn test_u128_public_shr_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 9, 0, 342, 345);
    }

    #[test]
    fn test_u128_public_shr_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 9, 0, 342, 345);
    }

    #[test]
    fn test_u128_private_shr_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 9, 0, 342, 345);
    }

    #[test]
    fn test_u128_private_shr_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 9, 0, 342, 345);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 9, 0, 342, 345);
    }

    #[test]
    fn test_i128_constant_shr_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 9, 0, 342, 345);
    }

    #[test]
    fn test_i128_public_shr_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 9, 0, 342, 345);
    }

    #[test]
    fn test_i128_private_shr_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 9, 0, 342, 345);
    }

    #[test]
    fn test_i128_public_shr_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 9, 0, 342, 345);
    }

    #[test]
    fn test_i128_public_shr_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 9, 0, 342, 345);
    }

    #[test]
    fn test_i128_private_shr_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 9, 0, 342, 345);
    }

    #[test]
    fn test_i128_private_shr_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 9, 0, 342, 345);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 45, 48);
    }

    #[test]
    fn test_u8_constant_shr_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 45, 48);
    }

    #[test]
    fn test_u8_public_shr_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 45, 48);
    }

    #[test]
    fn test_u8_private_shr_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 45, 48);
    }

    #[test]
    fn test_u8_public_shr_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 45, 48);
    }

    #[test]
    fn test_u8_public_shr_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 45, 48);
    }

    #[test]
    fn test_u8_private_shr_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 45, 48);
    }

    #[test]
    fn test_u8_private_shr_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 45, 48);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 45, 48);
    }

    #[test]
    fn test_i8_constant_shr_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 45, 48);
    }

    #[test]
    fn test_i8_public_shr_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 45, 48);
    }

    #[test]
    fn test_i8_private_shr_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 45, 48);
    }

    #[test]
    fn test_i8_public_shr_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 45, 48);
    }

    #[test]
    fn test_i8_public_shr_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 45, 48);
    }

    #[test]
    fn test_i8_private_shr_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 45, 48);
    }

    #[test]
    fn test_i8_private_shr_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 45, 48);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 70, 73);
    }

    #[test]
    fn test_u16_constant_shr_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 70, 73);
    }

    #[test]
    fn test_u16_public_shr_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 70, 73);
    }

    #[test]
    fn test_u16_private_shr_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 70, 73);
    }

    #[test]
    fn test_u16_public_shr_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 70, 73);
    }

    #[test]
    fn test_u16_public_shr_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 70, 73);
    }

    #[test]
    fn test_u16_private_shr_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 70, 73);
    }

    #[test]
    fn test_u16_private_shr_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 70, 73);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 70, 73);
    }

    #[test]
    fn test_i16_constant_shr_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 70, 73);
    }

    #[test]
    fn test_i16_public_shr_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 70, 73);
    }

    #[test]
    fn test_i16_private_shr_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 70, 73);
    }

    #[test]
    fn test_i16_public_shr_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 70, 73);
    }

    #[test]
    fn test_i16_public_shr_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 70, 73);
    }

    #[test]
    fn test_i16_private_shr_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 70, 73);
    }

    #[test]
    fn test_i16_private_shr_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 70, 73);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 119, 122);
    }

    #[test]
    fn test_u32_constant_shr_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 119, 122);
    }

    #[test]
    fn test_u32_public_shr_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 119, 122);
    }

    #[test]
    fn test_u32_private_shr_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 119, 122);
    }

    #[test]
    fn test_u32_public_shr_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 119, 122);
    }

    #[test]
    fn test_u32_public_shr_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 119, 122);
    }

    #[test]
    fn test_u32_private_shr_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 119, 122);
    }

    #[test]
    fn test_u32_private_shr_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 119, 122);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 119, 122);
    }

    #[test]
    fn test_i32_constant_shr_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 119, 122);
    }

    #[test]
    fn test_i32_public_shr_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 119, 122);
    }

    #[test]
    fn test_i32_private_shr_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 119, 122);
    }

    #[test]
    fn test_i32_public_shr_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 119, 122);
    }

    #[test]
    fn test_i32_public_shr_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 119, 122);
    }

    #[test]
    fn test_i32_private_shr_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 119, 122);
    }

    #[test]
    fn test_i32_private_shr_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 119, 122);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 216, 219);
    }

    #[test]
    fn test_u64_constant_shr_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 216, 219);
    }

    #[test]
    fn test_u64_public_shr_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 216, 219);
    }

    #[test]
    fn test_u64_private_shr_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 216, 219);
    }

    #[test]
    fn test_u64_public_shr_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 216, 219);
    }

    #[test]
    fn test_u64_public_shr_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 216, 219);
    }

    #[test]
    fn test_u64_private_shr_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 216, 219);
    }

    #[test]
    fn test_u64_private_shr_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 216, 219);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 216, 219);
    }

    #[test]
    fn test_i64_constant_shr_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 216, 219);
    }

    #[test]
    fn test_i64_public_shr_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 216, 219);
    }

    #[test]
    fn test_i64_private_shr_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 216, 219);
    }

    #[test]
    fn test_i64_public_shr_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 216, 219);
    }

    #[test]
    fn test_i64_public_shr_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 216, 219);
    }

    #[test]
    fn test_i64_private_shr_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 216, 219);
    }

    #[test]
    fn test_i64_private_shr_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 216, 219);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 9, 0, 350, 353);
    }

    #[test]
    fn test_u128_constant_shr_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 9, 0, 350, 353);
    }

    #[test]
    fn test_u128_public_shr_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 9, 0, 350, 353);
    }

    #[test]
    fn test_u128_private_shr_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 9, 0, 350, 3530);
    }

    #[test]
    fn test_u128_public_shr_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 9, 0, 350, 353);
    }

    #[test]
    fn test_u128_public_shr_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 9, 0, 350, 353);
    }

    #[test]
    fn test_u128_private_shr_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 9, 0, 350, 353);
    }

    #[test]
    fn test_u128_private_shr_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 9, 0, 350, 353);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 9, 0, 350, 353);
    }

    #[test]
    fn test_i128_constant_shr_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 9, 0, 350, 353);
    }

    #[test]
    fn test_i128_public_shr_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 9, 0, 350, 353);
    }

    #[test]
    fn test_i128_private_shr_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 9, 0, 350, 353);
    }

    #[test]
    fn test_i128_public_shr_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 9, 0, 350, 353);
    }

    #[test]
    fn test_i128_public_shr_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 9, 0, 350, 353);
    }

    #[test]
    fn test_i128_private_shr_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 9, 0, 350, 353);
    }

    #[test]
    fn test_i128_private_shr_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 9, 0, 350, 353);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 61, 64);
    }

    #[test]
    fn test_u8_constant_shr_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 61, 64);
    }

    #[test]
    fn test_u8_public_shr_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 61, 64);
    }

    #[test]
    fn test_u8_private_shr_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 61, 64);
    }

    #[test]
    fn test_u8_public_shr_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 61, 64);
    }

    #[test]
    fn test_u8_public_shr_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 61, 64);
    }

    #[test]
    fn test_u8_private_shr_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 61, 64);
    }

    #[test]
    fn test_u8_private_shr_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 61, 64);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 61, 64);
    }

    #[test]
    fn test_i8_constant_shr_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 61, 64);
    }

    #[test]
    fn test_i8_public_shr_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 61, 64);
    }

    #[test]
    fn test_i8_private_shr_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 61, 64);
    }

    #[test]
    fn test_i8_public_shr_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 61, 64);
    }

    #[test]
    fn test_i8_public_shr_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 61, 64);
    }

    #[test]
    fn test_i8_private_shr_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 61, 64);
    }

    #[test]
    fn test_i8_private_shr_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 61, 64);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 86, 89);
    }

    #[test]
    fn test_u16_constant_shr_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 86, 89);
    }

    #[test]
    fn test_u16_public_shr_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 86, 89);
    }

    #[test]
    fn test_u16_private_shr_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 86, 89);
    }

    #[test]
    fn test_u16_public_shr_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 86, 89);
    }

    #[test]
    fn test_u16_public_shr_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 86, 89);
    }

    #[test]
    fn test_u16_private_shr_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 86, 89);
    }

    #[test]
    fn test_u16_private_shr_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 86, 89);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 86, 89);
    }

    #[test]
    fn test_i16_constant_shr_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 86, 89);
    }

    #[test]
    fn test_i16_public_shr_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 86, 89);
    }

    #[test]
    fn test_i16_private_shr_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 86, 89);
    }

    #[test]
    fn test_i16_public_shr_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 86, 89);
    }

    #[test]
    fn test_i16_public_shr_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 86, 89);
    }

    #[test]
    fn test_i16_private_shr_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 86, 89);
    }

    #[test]
    fn test_i16_private_shr_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 86, 89);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 135, 138);
    }

    #[test]
    fn test_u32_constant_shr_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 135, 138);
    }

    #[test]
    fn test_u32_public_shr_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 135, 138);
    }

    #[test]
    fn test_u32_private_shr_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 135, 138);
    }

    #[test]
    fn test_u32_public_shr_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 135, 138);
    }

    #[test]
    fn test_u32_public_shr_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 135, 138);
    }

    #[test]
    fn test_u32_private_shr_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 135, 138);
    }

    #[test]
    fn test_u32_private_shr_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 135, 138);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 135, 138);
    }

    #[test]
    fn test_i32_constant_shr_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 135, 138);
    }

    #[test]
    fn test_i32_public_shr_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 135, 138);
    }

    #[test]
    fn test_i32_private_shr_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 135, 138);
    }

    #[test]
    fn test_i32_public_shr_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 135, 138);
    }

    #[test]
    fn test_i32_public_shr_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 135, 138);
    }

    #[test]
    fn test_i32_private_shr_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 135, 138);
    }

    #[test]
    fn test_i32_private_shr_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 135, 138);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 232, 235);
    }

    #[test]
    fn test_u64_constant_shr_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 232, 235);
    }

    #[test]
    fn test_u64_public_shr_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 232, 235);
    }

    #[test]
    fn test_u64_private_shr_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 232, 235);
    }

    #[test]
    fn test_u64_public_shr_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 232, 235);
    }

    #[test]
    fn test_u64_public_shr_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 232, 235);
    }

    #[test]
    fn test_u64_private_shr_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 232, 235);
    }

    #[test]
    fn test_u64_private_shr_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 232, 235);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 3, 0, 232, 235);
    }

    #[test]
    fn test_i64_constant_shr_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 3, 0, 232, 235);
    }

    #[test]
    fn test_i64_public_shr_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 3, 0, 232, 235);
    }

    #[test]
    fn test_i64_private_shr_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 3, 0, 232, 235);
    }

    #[test]
    fn test_i64_public_shr_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 3, 0, 232, 235);
    }

    #[test]
    fn test_i64_public_shr_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 3, 0, 232, 235);
    }

    #[test]
    fn test_i64_private_shr_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 3, 0, 232, 235);
    }

    #[test]
    fn test_i64_private_shr_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 3, 0, 232, 235);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 9, 0, 366, 369);
    }

    #[test]
    fn test_u128_constant_shr_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 9, 0, 366, 369);
    }

    #[test]
    fn test_u128_public_shr_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 9, 0, 366, 369);
    }

    #[test]
    fn test_u128_private_shr_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 9, 0, 366, 369);
    }

    #[test]
    fn test_u128_public_shr_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 9, 0, 366, 369);
    }

    #[test]
    fn test_u128_public_shr_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 9, 0, 366, 369);
    }

    #[test]
    fn test_u128_private_shr_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 9, 0, 366, 369);
    }

    #[test]
    fn test_u128_private_shr_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 9, 0, 366, 369);
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
        run_test::<I, M>(Mode::Constant, Mode::Public, 9, 0, 366, 369);
    }

    #[test]
    fn test_i128_constant_shr_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Private, 9, 0, 366, 369);
    }

    #[test]
    fn test_i128_public_shr_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Constant, 9, 0, 366, 369);
    }

    #[test]
    fn test_i128_private_shr_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Constant, 9, 0, 366, 369);
    }

    #[test]
    fn test_i128_public_shr_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 9, 0, 366, 369);
    }

    #[test]
    fn test_i128_public_shr_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 9, 0, 366, 369);
    }

    #[test]
    fn test_i128_private_shr_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 9, 0, 366, 369);
    }

    #[test]
    fn test_i128_private_shr_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 9, 0, 366, 369);
    }

    // Exhaustive tests for u8, where shift magnitude is u8

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
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 5, 0, 39, 42);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 5, 0, 39, 42);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Constant, 5, 0, 39, 42);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Constant, 5, 0, 39, 42);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 5, 0, 39, 42);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 5, 0, 39, 42);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 5, 0, 39, 42);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 5, 0, 39, 42);
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
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 68, 0, 142, 153);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 68, 0, 142, 153);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Constant, 68, 0, 142, 153);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Constant, 68, 0, 142, 153);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 68, 0, 142, 153);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 68, 0, 142, 153);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 68, 0, 142, 153);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 68, 0, 142, 153);
    }
}
