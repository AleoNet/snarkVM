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

use crate::{BaseField, One, RippleCarryAdder, SignExtend, Zero};
use snarkvm_fields::PrimeField;
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

        // Compute double and add algorithm
        let mut to_add = Vec::new();
        let mut a_shifted = Vec::new();
        for (i, b_bit) in b.iter().enumerate() {
            // double
            a_shifted.extend(iter::repeat(Boolean::new(mode, false)).take(i));
            a_shifted.extend_from_slice(&a);
            a_shifted.truncate(SIZE);

            // conditionally add
            to_add.reserve(a_shifted.len());
            for a_bit in a_shifted.iter() {
                let selected_bit = Boolean::ternary(b_bit, a_bit, &Boolean::new(mode, false));

                to_add.push(selected_bit);
            }

            bits = bits.add_bits(&to_add);
            let _carry = bits.pop();
            to_add.clear();
            a_shifted.clear();
        }
        drop(to_add);
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
    use crate::Circuit;
    use num_traits::CheckedMul;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 10;

    fn check_mul(
        name: &str,
        expected: i64,
        a: &Signed<Circuit, i64, u64, 64>,
        b: &Signed<Circuit, i64, u64, 64>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate = a * b;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} * {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            // assert_eq!(num_constants, scope.num_constants_in_scope());
            // assert_eq!(num_public, scope.num_public_in_scope());
            // assert_eq!(num_private, scope.num_private_in_scope());
            // assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    fn check_mul_assign(
        name: &str,
        expected: i64,
        a: &Signed<Circuit, i64, u64, 64>,
        b: &Signed<Circuit, i64, u64, 64>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let mut candidate = a.clone();
            candidate *= b;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} * {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            // assert_eq!(num_constants, scope.num_constants_in_scope());
            // assert_eq!(num_public, scope.num_public_in_scope());
            // assert_eq!(num_private, scope.num_private_in_scope());
            // assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    #[test]
    fn test_constant_times_constant() {
        for i in 0..ITERATIONS {
            let multiplicand: i64 = UniformRand::rand(&mut thread_rng());
            let multiplier: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match multiplicand.checked_mul(multiplier) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Constant, multiplicand);
            let b = Signed::new(Mode::Constant, multiplier);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, expected, &a, &b, 1757, 0, 0, 0);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, expected, &a, &b, 1757, 0, 0, 0);
        }
    }

    #[test]
    fn test_constant_times_public() {
        for i in 0..ITERATIONS {
            let multiplicand: i64 = UniformRand::rand(&mut thread_rng());
            let multiplier: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match multiplicand.checked_mul(multiplier) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Constant, multiplicand);
            let b = Signed::new(Mode::Public, multiplier);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, expected, &a, &b, 757, 0, 2500, 2500);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, expected, &a, &b, 757, 0, 2500, 2500);
        }
    }

    #[test]
    fn test_constant_times_private() {
        for i in 0..ITERATIONS {
            let multiplicand: i64 = UniformRand::rand(&mut thread_rng());
            let multiplier: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match multiplicand.checked_mul(multiplier) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Constant, multiplicand);
            let b = Signed::new(Mode::Private, multiplier);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, expected, &a, &b, 757, 0, 2500, 2500);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, expected, &a, &b, 757, 0, 2500, 2500);
        }
    }

    #[test]
    fn test_public_times_public() {
        for i in 0..ITERATIONS {
            let multiplicand: i64 = UniformRand::rand(&mut thread_rng());
            let multiplier: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match multiplicand.checked_mul(multiplier) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Public, multiplicand);
            let b = Signed::new(Mode::Public, multiplier);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_public_times_private() {
        for i in 0..ITERATIONS {
            let multiplicand: i64 = UniformRand::rand(&mut thread_rng());
            let multiplier: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match multiplicand.checked_mul(multiplier) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Public, multiplicand);
            let b = Signed::new(Mode::Private, multiplier);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_private_times_public() {
        for i in 0..ITERATIONS {
            let multiplicand: i64 = UniformRand::rand(&mut thread_rng());
            let multiplier: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match multiplicand.checked_mul(multiplier) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Private, multiplicand);
            let b = Signed::new(Mode::Public, multiplier);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_private_times_private() {
        for i in 0..ITERATIONS {
            let multiplicand: i64 = UniformRand::rand(&mut thread_rng());
            let multiplier: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match multiplicand.checked_mul(multiplier) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::new(Mode::Private, multiplicand);
            let b = Signed::new(Mode::Private, multiplier);

            let name = format!("Mul: a * b {}", i);
            check_mul(&name, expected, &a, &b, 755, 0, 3255, 3255);
            let name = format!("MulAssign: a * b {}", i);
            check_mul_assign(&name, expected, &a, &b, 755, 0, 3255, 3255);
        }
    }

    #[test]
    fn test_mul_matches() {
        for i in 0..ITERATIONS {
            let multiplicand: i64 = UniformRand::rand(&mut thread_rng());
            let multiplier: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match multiplicand.checked_mul(multiplier) {
                Some(expected) => expected,
                None => continue,
            };

            // Constant
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, multiplicand);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, multiplier);
            let candidate = a * b;
            assert_eq!(expected, candidate.eject_value());

            // Private
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Private, multiplicand);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Private, multiplier);
            let candidate = a * b;
            assert_eq!(expected, candidate.eject_value());
        }
    }
}
