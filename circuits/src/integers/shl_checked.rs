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

impl<E: Environment, I: IntegerType, M: private::Magnitude> ShlChecked<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    #[inline]
    fn shl_checked(&self, rhs: &Integer<E, M>) -> Self::Output {
        // Determine the variable mode.
        if self.is_constant() && rhs.is_constant() {
            // This cast is safe since `Magnitude`s can only be `u8`, `u16`, or `u32`.
            match self.eject_value().checked_shl(rhs.eject_value().to_u32().unwrap()) {
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

            // Perform the left shift operation by exponentiation and multiplication.
            // By enforcing that the upper bits are zero, we have that rhs < I::BITS.
            // Therefore, 2^{rhs} < I::MAX.
            let mut lower_rhs_bits = Vec::with_capacity(8);
            lower_rhs_bits.extend_from_slice(&rhs.bits_le[..first_upper_bit_index]);
            lower_rhs_bits.resize(8, Boolean::new(Mode::Constant, false));

            // Use U8 for the exponent as it costs fewer constraints.
            let rhs_as_u8 = U8::<E> { bits_le: lower_rhs_bits, phantom: Default::default() };

            if rhs_as_u8.is_constant() {
                println!("RHS is a constant.");
                // If the shift amount is a constant, then we can manually shift in bits and truncate the result.
                let shift_amount = rhs_as_u8.eject_value();
                let mut bits_le = vec![Boolean::new(self.eject_mode(), false); shift_amount as usize];

                bits_le.extend_from_slice(&self.bits_le);
                bits_le.truncate(I::BITS);

                Self { bits_le, phantom: Default::default() }
            } else {
                let shift_as_multiplicand = Self::new(Mode::Constant, I::one() + I::one()).pow_wrapped(&rhs_as_u8);
                self.mul_wrapped(&shift_as_multiplicand)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 128;

    #[rustfmt::skip]
    fn check_shl_checked<I: IntegerType, M: private::Magnitude>(
        name: &str,
        expected: I,
        a: &Integer<Circuit, I>,
        b: &Integer<Circuit, M>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, || {
            let case = format!("({} << {})", a.eject_value(), b.eject_value());

            let candidate = a.shl_checked(b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := {}",
                expected,
                candidate.eject_value(),
                case
            );

            print!("Constants: {:?}, ", Circuit::num_constants_in_scope());
            print!("Public: {:?}, ", Circuit::num_public_in_scope());
            print!("Private: {:?}, ", Circuit::num_private_in_scope());
            print!("Constraints: {:?}\n", Circuit::num_constraints_in_scope());
            println!("Circuit: {}", Circuit);

            // assert_eq!(num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", case);
            // assert_eq!(num_public, Circuit::num_public_in_scope(), "{} (num_public)", case);
            // assert_eq!(num_private, Circuit::num_private_in_scope(), "{} (num_private)", case);
            // assert_eq!(num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", case);
            assert!(Circuit::is_satisfied(), "{} (is_satisfied)", case);
        });
        Circuit::reset()
    }

    #[rustfmt::skip]
    fn check_shl_halts<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        value_a: I,
        value_b: M,
    ) {
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        let result = std::panic::catch_unwind(|| a.shl_checked(&b));
        assert!(result.is_err());
    }

    #[rustfmt::skip]
    fn check_shl_fails<I: IntegerType + std::panic::RefUnwindSafe, M: private::Magnitude + std::panic::RefUnwindSafe>(
        mode_a: Mode,
        mode_b: Mode,
        value_a: I,
        value_b: M,
    ) {
        let name = format!("Shl: {} << {} exceeds bit width", value_a, value_b);
        let a = Integer::<Circuit, I>::new(mode_a, value_a);
        let b = Integer::new(mode_b, value_b);
        Circuit::scoped(&name, || {
            let case = format!("({} << {})", a.eject_value(), b.eject_value());

            println!("B BITS: {:?}", b.bits_le);

            let _candidate = a.shl_checked(&b);

            print!("Constants: {:?}, ", Circuit::num_constants_in_scope());
            print!("Public: {:?}, ", Circuit::num_public_in_scope());
            print!("Private: {:?}, ", Circuit::num_private_in_scope());
            print!("Constraints: {:?}\n", Circuit::num_constraints_in_scope());
            assert!(!Circuit::is_satisfied(), "{} (!is_satisfied)", case);
        });
        Circuit::reset();
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
        let check_shl = | name: String, first: I, second: M | {
            match first.checked_shl(second.to_u32().unwrap()) {
                Some(value) => {
                    let a = Integer::<Circuit, I>::new(mode_a, first);
                    let b = Integer::<Circuit, M>::new(mode_b, second);

                    check_shl_checked::<I, M>(&name, value, &a, &b, num_constants, num_public, num_private, num_constraints)
                }
                None => match (mode_a, mode_b) {
                    (_, Mode::Constant) => check_shl_halts::<I, M>(mode_a, mode_b, first, second),
                    _ => check_shl_fails::<I, M>(mode_a, mode_b, first, second),
                },
            };
        };

        for i in 0..ITERATIONS {
            let name = format!("Shl: {} << {} {}", mode_a, mode_b, i);
            let first: I = UniformRand::rand(&mut thread_rng());
            let second: M = UniformRand::rand(&mut thread_rng());

            check_shl(name, first, second);

            // Check that shift left by one is computed correctly.
            let name = format!("Double: {} << {} {}", mode_a, mode_b, i);
            check_shl(name, first, M::one());
        }
    }

    // Tests for u8, where shift magnitude is u8

    #[test]
    fn test_u8_constant_shl_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shl_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shl_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shl_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_shl_u8_constant() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shl_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_public_shl_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_private_shl_u8_public() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_u8_private_shl_u8_private() {
        type I = u8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
    }

    // Tests for i8, where shift magnitude is u8

    #[test]
    fn test_i8_constant_shl_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shl_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shl_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shl_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_shl_u8_constant() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shl_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_public_shl_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_private_shl_u8_public() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 46, 0, 349, 364);
    }

    #[test]
    fn test_i8_private_shl_u8_private() {
        type I = i8;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 46, 0, 349, 364);
    }

    // Tests for u16, where shift magnitude is u8

    #[test]
    fn test_u16_constant_shl_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shl_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shl_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shl_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_shl_u8_constant() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shl_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_public_shl_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_private_shl_u8_public() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_u16_private_shl_u8_private() {
        type I = u16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 62, 0, 653, 668);
    }

    // Tests for i16, where shift magnitude is u8

    #[test]
    fn test_i16_constant_shl_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shl_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shl_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shl_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_shl_u8_constant() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shl_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_public_shl_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_private_shl_u8_public() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 62, 0, 653, 668);
    }

    #[test]
    fn test_i16_private_shl_u8_private() {
        type I = i16;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 62, 0, 653, 668);
    }

    // Tests for u32, where shift magnitude is u8

    #[test]
    fn test_u32_constant_shl_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shl_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shl_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shl_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_shl_u8_constant() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shl_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_public_shl_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_private_shl_u8_public() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_u32_private_shl_u8_private() {
        type I = u32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1261, 1276);
    }

    // Tests for i32, where shift magnitude is u8

    #[test]
    fn test_i32_constant_shl_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shl_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shl_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shl_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_shl_u8_constant() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shl_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_public_shl_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_private_shl_u8_public() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1261, 1276);
    }

    #[test]
    fn test_i32_private_shl_u8_private() {
        type I = i32;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1261, 1276);
    }

    // Tests for u64, where shift magnitude is u8

    #[test]
    fn test_u64_constant_shl_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shl_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shl_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shl_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_shl_u8_constant() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shl_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_public_shl_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_private_shl_u8_public() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_u64_private_shl_u8_private() {
        type I = u64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2477, 2492);
    }

    // Tests for i64, where shift magnitude is u8

    #[test]
    fn test_i64_constant_shl_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shl_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shl_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shl_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_shl_u8_constant() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shl_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_public_shl_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_private_shl_u8_public() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2477, 2492);
    }

    #[test]
    fn test_i64_private_shl_u8_private() {
        type I = i64;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2477, 2492);
    }

    // Tests for u128, where shift magnitude is u8

    #[test]
    fn test_u128_constant_shl_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shl_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shl_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shl_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_shl_u8_constant() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shl_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_public_shl_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_private_shl_u8_public() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_u128_private_shl_u8_private() {
        type I = u128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 376, 0, 4024, 4039);
    }

    // Tests for i128, where shift magnitude is u8

    #[test]
    fn test_i128_constant_shl_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shl_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Public, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shl_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Constant, Mode::Private, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shl_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_shl_u8_constant() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shl_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_public_shl_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Public, Mode::Private, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_private_shl_u8_public() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Public, 376, 0, 4024, 4039);
    }

    #[test]
    fn test_i128_private_shl_u8_private() {
        type I = i128;
        type M = u8;
        run_test::<I, M>(Mode::Private, Mode::Private, 376, 0, 4024, 4039);
    }

    // Tests for u8, where shift magnitude is u16

    #[test]
    fn test_u8_constant_shl_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shl_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Public, 16, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shl_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Private, 16, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shl_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_shl_u16_constant() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shl_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_public_shl_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_private_shl_u16_public() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_u8_private_shl_u16_private() {
        type I = u8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 78, 0, 717, 748);
    }

    // Tests for i8, where shift magnitude is u16

    #[test]
    fn test_i8_constant_shl_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shl_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shl_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shl_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_shl_u16_constant() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shl_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_public_shl_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_private_shl_u16_public() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 78, 0, 717, 748);
    }

    #[test]
    fn test_i8_private_shl_u16_private() {
        type I = i8;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 78, 0, 717, 748);
    }

    // Tests for u16, where shift magnitude is u16

    #[test]
    fn test_u16_constant_shl_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shl_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shl_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shl_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_shl_u16_constant() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shl_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_public_shl_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_private_shl_u16_public() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_u16_private_shl_u16_private() {
        type I = u16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1341, 1372);
    }

    // Tests for i16, where shift magnitude is u16

    #[test]
    fn test_i16_constant_shl_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shl_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shl_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shl_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_shl_u16_constant() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shl_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_public_shl_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_private_shl_u16_public() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 94, 0, 1341, 1372);
    }

    #[test]
    fn test_i16_private_shl_u16_private() {
        type I = i16;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 94, 0, 1341, 1372);
    }

    // Tests for u32, where shift magnitude is u16

    #[test]
    fn test_u32_constant_shl_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shl_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shl_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shl_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_shl_u16_constant() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shl_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_public_shl_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_private_shl_u16_public() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_u32_private_shl_u16_private() {
        type I = u32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 126, 0, 2589, 2620);
    }

    // Tests for i32, where shift magnitude is u16

    #[test]
    fn test_i32_constant_shl_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shl_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shl_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shl_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_shl_u16_constant() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shl_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_public_shl_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_private_shl_u16_public() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 126, 0, 2589, 2620);
    }

    #[test]
    fn test_i32_private_shl_u16_private() {
        type I = i32;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 126, 0, 2589, 2620);
    }

    // Tests for u64, where shift magnitude is u16

    #[test]
    fn test_u64_constant_shl_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shl_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shl_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shl_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_shl_u16_constant() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shl_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_public_shl_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_private_shl_u16_public() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_u64_private_shl_u16_private() {
        type I = u64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5085, 5116);
    }

    // Tests for i64, where shift magnitude is u16

    #[test]
    fn test_i64_constant_shl_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shl_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shl_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shl_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_shl_u16_constant() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shl_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_public_shl_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_private_shl_u16_public() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5085, 5116);
    }

    #[test]
    fn test_i64_private_shl_u16_private() {
        type I = i64;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5085, 5116);
    }

    // Tests for u128, where shift magnitude is u16

    #[test]
    fn test_u128_constant_shl_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shl_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shl_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shl_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_shl_u16_constant() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shl_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_public_shl_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_private_shl_u16_public() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_u128_private_shl_u16_private() {
        type I = u128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 504, 0, 8248, 8279);
    }

    // Tests for i128, where shift magnitude is u16

    #[test]
    fn test_i128_constant_shl_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shl_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shl_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shl_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_shl_u16_constant() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shl_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_public_shl_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Public, Mode::Private, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_private_shl_u16_public() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Public, 504, 0, 8248, 8279);
    }

    #[test]
    fn test_i128_private_shl_u16_private() {
        type I = i128;
        type M = u16;
        run_test::<I, M>(Mode::Private, Mode::Private, 504, 0, 8248, 8279);
    }

    // Tests for u8, where shift magnitude is u32

    #[test]
    fn test_u8_constant_shl_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shl_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u8_constant_shl_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shl_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u8_private_shl_u32_constant() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u8_public_shl_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_public_shl_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_private_shl_u32_public() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_u8_private_shl_u32_private() {
        type I = u8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 142, 0, 1453, 1516);
    }

    // Tests for i8, where shift magnitude is u32

    #[test]
    fn test_i8_constant_shl_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 8, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shl_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i8_constant_shl_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shl_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i8_private_shl_u32_constant() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i8_public_shl_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_public_shl_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_private_shl_u32_public() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 142, 0, 1453, 1516);
    }

    #[test]
    fn test_i8_private_shl_u32_private() {
        type I = i8;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 142, 0, 1453, 1516);
    }

    // Tests for u16, where shift magnitude is u32

    #[test]
    fn test_u16_constant_shl_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shl_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_constant_shl_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shl_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_private_shl_u32_constant() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u16_public_shl_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_public_shl_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_private_shl_u32_public() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_u16_private_shl_u32_private() {
        type I = u16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2717, 2780);
    }

    // Tests for i16, where shift magnitude is u32

    #[test]
    fn test_i16_constant_shl_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shl_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_constant_shl_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shl_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_private_shl_u32_constant() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i16_public_shl_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_public_shl_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_private_shl_u32_public() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 158, 0, 2717, 2780);
    }

    #[test]
    fn test_i16_private_shl_u32_private() {
        type I = i16;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 158, 0, 2717, 2780);
    }

    // Tests for u32, where shift magnitude is u32

    #[test]
    fn test_u32_constant_shl_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shl_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_constant_shl_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shl_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_private_shl_u32_constant() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u32_public_shl_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_public_shl_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_private_shl_u32_public() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_u32_private_shl_u32_private() {
        type I = u32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5245, 5308);
    }

    // Tests for i32, where shift magnitude is u32

    #[test]
    fn test_i32_constant_shl_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 32, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shl_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_constant_shl_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shl_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_private_shl_u32_constant() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i32_public_shl_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_public_shl_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_private_shl_u32_public() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 190, 0, 5245, 5308);
    }

    #[test]
    fn test_i32_private_shl_u32_private() {
        type I = i32;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 190, 0, 5245, 5308);
    }

    // Tests for u64, where shift magnitude is u32

    #[test]
    fn test_u64_constant_shl_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shl_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_constant_shl_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shl_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_private_shl_u32_constant() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u64_public_shl_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_public_shl_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_private_shl_u32_public() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_u64_private_shl_u32_private() {
        type I = u64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 254, 0, 10301, 10364);
    }

    // Tests for i64, where shift magnitude is u32

    #[test]
    fn test_i64_constant_shl_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 64, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shl_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_constant_shl_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shl_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_private_shl_u32_constant() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i64_public_shl_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_public_shl_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_private_shl_u32_public() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 254, 0, 10301, 10364);
    }

    #[test]
    fn test_i64_private_shl_u32_private() {
        type I = i64;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 254, 0, 10301, 10364);
    }

    // Tests for u128, where shift magnitude is u32

    #[test]
    fn test_u128_constant_shl_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shl_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_constant_shl_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shl_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_private_shl_u32_constant() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_u128_public_shl_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_public_shl_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_private_shl_u32_public() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_u128_private_shl_u32_private() {
        type I = u128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 760, 0, 16696, 16759);
    }

    // Tests for i128, where shift magnitude is u32

    #[test]
    fn test_i128_constant_shl_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 128, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shl_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_constant_shl_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shl_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_private_shl_u32_constant() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Constant, Mode::Constant, 16, 0, 0, 0);
    }

    #[test]
    fn test_i128_public_shl_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_public_shl_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Public, Mode::Private, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_private_shl_u32_public() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Public, 760, 0, 16696, 16759);
    }

    #[test]
    fn test_i128_private_shl_u32_private() {
        type I = i128;
        type M = u32;
        run_test::<I, M>(Mode::Private, Mode::Private, 760, 0, 16696, 16759);
    }
}
