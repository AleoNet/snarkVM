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

impl<E: Environment, I: IntegerType, M: private::Magnitude> ShrWrapped<Integer<E, M>> for Integer<E, I> {
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
            lower_rhs_bits.resize(8, Boolean::new(Mode::Constant, false));

            // Use U8 for the exponent as it costs fewer constraints.
            let rhs_as_u8 = U8 { bits_le: lower_rhs_bits, phantom: Default::default() };

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
                let shift_as_divisor = &Self::new(Mode::Constant, I::one() + I::one()).pow_wrapped(&rhs_as_u8);
                if I::is_signed() {
                    // This is safe as I::BITS is always greater than zero.
                    let self_is_negative = self.bits_le.last().unwrap();
                    let result = &self.div_wrapped(shift_as_divisor);

                    let result_in_field =
                        BaseField::from_bits_le(Mode::Private, &(!result).bits_le).add(BaseField::one());
                    let self_in_field = BaseField::from_bits_le(Mode::Private, &(!self).bits_le).add(BaseField::one());
                    let shift_as_divisor_in_field = BaseField::from_bits_le(Mode::Private, &shift_as_divisor.bits_le);
                    let result_is_exact = self_in_field.is_eq(&result_in_field.mul(&shift_as_divisor_in_field));

                    println!(
                        "SelfIsNegative: {:?}, Self: {:?}, Result: {:?}, Shift: {:?}, ResultExact: {:?}",
                        self_is_negative,
                        self.eject_value(),
                        result.eject_value(),
                        shift_as_divisor.eject_value(),
                        result_is_exact.eject_value()
                    );

                    Self::ternary(
                        &(!self_is_negative).or(&self_is_negative.and(&result_is_exact)),
                        &result,
                        &(&result).sub(Self::one()),
                    )
                } else {
                    self.div_wrapped(shift_as_divisor)
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

    use num_traits::CheckedShr;
    use rand::thread_rng;
    use std::ops::Range;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_shr_without_expected_numbers<I: CheckedShr + IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        name: &str,
        first: I,
        second: M,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let expected = first.wrapping_shr(second.to_u32().unwrap());
        let a = Integer::<Circuit, I>::new(mode_a, first);
        let b = Integer::<Circuit, M>::new(mode_b, second);
        let case = format!("({} >> {})", a.eject_value(), b.eject_value());
        check_binary_operation_passes_without_expected_numbers(name, &case, expected, &a, &b, Integer::shr_wrapped);
    }

    #[rustfmt::skip]
    fn check_shr<I: CheckedShr + IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
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
        check_binary_operation_passes(name, &case, expected, &a, &b, Integer::shr_wrapped, num_constants, num_public, num_private, num_constraints);
    }

    #[rustfmt::skip]
    fn run_test_without_expected_numbers<I: CheckedShr + IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let check_shr = |name: &str, first: I, second: M| check_shr_without_expected_numbers(name, first, second, mode_a, mode_b);

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
    fn run_test<I: CheckedShr + IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
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
    fn run_exhaustive_test_without_expected_numbers<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
    ) where
        Range<I>: Iterator<Item = I>,
        Range<M>: Iterator<Item = M>
    {
        for first in I::MIN..I::MAX {
            for second in M::MIN..M::MAX {
                let name = format!("Shr: ({} >> {})", first, second);
                check_shr_without_expected_numbers(&name, first, second, mode_a, mode_b);
            }
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_public_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_private_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_private_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_public_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_private_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_private_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_shr_u8_private() {
        type I = u16;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_shr_u8_constant() {
        type I = u16;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_shr_u8_constant() {
        type I = u16;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_shr_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_public_shr_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_private_shr_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_private_shr_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 62, 0, 653, 668);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_shr_u8_private() {
        type I = i16;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_shr_u8_constant() {
        type I = i16;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_shr_u8_constant() {
        type I = i16;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_shr_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_public_shr_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_private_shr_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_private_shr_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 62, 0, 653, 668);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_shr_u8_private() {
        type I = u32;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_shr_u8_constant() {
        type I = u32;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_shr_u8_constant() {
        type I = u32;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_shr_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_public_shr_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_private_shr_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_private_shr_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1261, 1276);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_shr_u8_private() {
        type I = i32;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_shr_u8_constant() {
        type I = i32;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_shr_u8_constant() {
        type I = i32;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_shr_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_public_shr_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_private_shr_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_private_shr_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1261, 1276);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_shr_u8_private() {
        type I = u64;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_shr_u8_constant() {
        type I = u64;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_shr_u8_constant() {
        type I = u64;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_shr_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_public_shr_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_private_shr_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_private_shr_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2477, 2492);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_shr_u8_private() {
        type I = i64;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_shr_u8_constant() {
        type I = i64;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_shr_u8_constant() {
        type I = i64;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_shr_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_public_shr_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_private_shr_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_private_shr_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2477, 2492);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_shr_u8_private() {
        type I = u128;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_shr_u8_constant() {
        type I = u128;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_shr_u8_constant() {
        type I = u128;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_shr_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_public_shr_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_private_shr_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_private_shr_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 376, 0, 4024, 4039);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_shr_u8_private() {
        type I = i128;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_shr_u8_constant() {
        type I = i128;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_shr_u8_constant() {
        type I = i128;
        type M = u8;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_shr_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_public_shr_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_private_shr_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_private_shr_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 376, 0, 4024, 4039);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_shr_u16_private() {
        type I = u8;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_shr_u16_constant() {
        type I = u8;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_shr_u16_constant() {
        type I = u8;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_shr_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_public_shr_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_private_shr_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_private_shr_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 78, 0, 717, 748);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_shr_u16_private() {
        type I = i8;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_shr_u16_constant() {
        type I = i8;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_shr_u16_constant() {
        type I = i8;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_shr_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_public_shr_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_private_shr_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_private_shr_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 78, 0, 717, 748);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_shr_u16_private() {
        type I = u16;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_shr_u16_constant() {
        type I = u16;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_shr_u16_constant() {
        type I = u16;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_shr_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_public_shr_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_private_shr_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_private_shr_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1341, 1372);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_shr_u16_private() {
        type I = i16;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_shr_u16_constant() {
        type I = i16;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_shr_u16_constant() {
        type I = i16;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_shr_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_public_shr_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_private_shr_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_private_shr_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1341, 1372);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_shr_u16_private() {
        type I = u32;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_shr_u16_constant() {
        type I = u32;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_shr_u16_constant() {
        type I = u32;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_shr_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_public_shr_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_private_shr_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_private_shr_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 126, 0, 2589, 2620);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_shr_u16_private() {
        type I = i32;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_shr_u16_constant() {
        type I = i32;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_shr_u16_constant() {
        type I = i32;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_shr_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_public_shr_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_private_shr_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_private_shr_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 126, 0, 2589, 2620);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_shr_u16_private() {
        type I = u64;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_shr_u16_constant() {
        type I = u64;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_shr_u16_constant() {
        type I = u64;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_shr_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_public_shr_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_private_shr_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_private_shr_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5085, 5116);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_shr_u16_private() {
        type I = i64;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_shr_u16_constant() {
        type I = i64;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_shr_u16_constant() {
        type I = i64;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_shr_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_public_shr_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_private_shr_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_private_shr_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5085, 5116);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_shr_u16_private() {
        type I = u128;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_shr_u16_constant() {
        type I = u128;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_shr_u16_constant() {
        type I = u128;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_shr_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_public_shr_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_private_shr_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_private_shr_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 504, 0, 8248, 8279);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_shr_u16_private() {
        type I = i128;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_shr_u16_constant() {
        type I = i128;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_shr_u16_constant() {
        type I = i128;
        type M = u16;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_shr_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_public_shr_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_private_shr_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_private_shr_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 504, 0, 8248, 8279);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u8_constant_shr_u32_private() {
        type I = u8;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u8_public_shr_u32_constant() {
        type I = u8;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u8_private_shr_u32_constant() {
        type I = u8;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u8_public_shr_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_public_shr_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_private_shr_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_private_shr_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 142, 0, 1453, 1516);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i8_constant_shr_u32_private() {
        type I = i8;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i8_public_shr_u32_constant() {
        type I = i8;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i8_private_shr_u32_constant() {
        type I = i8;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i8_public_shr_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_public_shr_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_private_shr_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_private_shr_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 142, 0, 1453, 1516);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u16_constant_shr_u32_private() {
        type I = u16;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u16_public_shr_u32_constant() {
        type I = u16;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u16_private_shr_u32_constant() {
        type I = u16;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u16_public_shr_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_public_shr_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_private_shr_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_private_shr_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2717, 2780);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i16_constant_shr_u32_private() {
        type I = i16;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i16_public_shr_u32_constant() {
        type I = i16;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i16_private_shr_u32_constant() {
        type I = i16;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i16_public_shr_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_public_shr_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_private_shr_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_private_shr_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2717, 2780);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u32_constant_shr_u32_private() {
        type I = u32;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u32_public_shr_u32_constant() {
        type I = u32;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u32_private_shr_u32_constant() {
        type I = u32;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u32_public_shr_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_public_shr_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_private_shr_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_private_shr_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5245, 5308);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i32_constant_shr_u32_private() {
        type I = i32;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i32_public_shr_u32_constant() {
        type I = i32;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i32_private_shr_u32_constant() {
        type I = i32;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i32_public_shr_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_public_shr_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_private_shr_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_private_shr_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5245, 5308);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u64_constant_shr_u32_private() {
        type I = u64;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u64_public_shr_u32_constant() {
        type I = u64;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u64_private_shr_u32_constant() {
        type I = u64;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u64_public_shr_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_public_shr_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_private_shr_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_private_shr_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 254, 0, 10301, 10364);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i64_constant_shr_u32_private() {
        type I = i64;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i64_public_shr_u32_constant() {
        type I = i64;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i64_private_shr_u32_constant() {
        type I = i64;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i64_public_shr_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_public_shr_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_private_shr_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_private_shr_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 254, 0, 10301, 10364);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_u128_constant_shr_u32_private() {
        type I = u128;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_u128_public_shr_u32_constant() {
        type I = u128;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_u128_private_shr_u32_constant() {
        type I = u128;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_u128_public_shr_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_public_shr_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_private_shr_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_private_shr_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 760, 0, 16696, 16759);
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
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_i128_constant_shr_u32_private() {
        type I = i128;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_i128_public_shr_u32_constant() {
        type I = i128;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_i128_private_shr_u32_constant() {
        type I = i128;
        type M = u32;
        run_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_i128_public_shr_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_public_shr_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_private_shr_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_private_shr_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 760, 0, 16696, 16759);
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
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_constant_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shr_u8_constant() {
        type I = u8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_public_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shr_u8_public() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_u8_private_shr_u8_private() {
        type I = u8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
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
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Public);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_constant_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Constant, Mode::Private);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Public, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shr_u8_constant() {
        type I = i8;
        type M = u8;
        run_exhaustive_test_without_expected_numbers::<I, M>(Mode::Private, Mode::Constant);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_public_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shr_u8_public() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    #[ignore]
    fn test_exhaustive_i8_private_shr_u8_private() {
        type I = i8;
        type M = u8;
        run_exhaustive_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
    }
}
