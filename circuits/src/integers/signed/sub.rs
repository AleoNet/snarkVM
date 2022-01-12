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

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Sub<Self>
    for Signed<E, I, U, SIZE>
{
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self - &other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Sub<&Self>
    for Signed<E, I, U, SIZE>
{
    type Output = Self;

    fn sub(self, other: &Self) -> Self::Output {
        self + -other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>
    Sub<Signed<E, I, U, SIZE>> for &Signed<E, I, U, SIZE>
{
    type Output = Signed<E, I, U, SIZE>;

    fn sub(self, other: Signed<E, I, U, SIZE>) -> Self::Output {
        (*self).clone() - other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize>
    Sub<&Signed<E, I, U, SIZE>> for &Signed<E, I, U, SIZE>
{
    type Output = Signed<E, I, U, SIZE>;

    fn sub(self, other: &Signed<E, I, U, SIZE>) -> Self::Output {
        (*self).clone() - other
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> SubAssign<Self>
    for Signed<E, I, U, SIZE>
{
    fn sub_assign(&mut self, other: Self) {
        *self -= &other;
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> SubAssign<&Self>
    for Signed<E, I, U, SIZE>
{
    fn sub_assign(&mut self, other: &Self) {
        *self = self.clone() + -other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_sub(
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
            let candidate = a - b;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} - {})",
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

    fn check_sub_assign(
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
            candidate -= b;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} - {})",
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
    fn test_constant_minus_constant() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, expected, &a, &b, 4, 0, 0, 0);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, expected, &a, &b, 4, 0, 0, 0);
        }
    }

    #[test]
    fn test_constant_minus_public() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, expected, &a, &b, 2, 0, 3, 3);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_public_minus_constant() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, expected, &a, &b, 2, 0, 3, 3);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_constant_minus_private() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, expected, &a, &b, 2, 0, 3, 3);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_private_minus_constant() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, expected, &a, &b, 2, 0, 3, 3);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_public_minus_public() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, expected, &a, &b, 2, 0, 6, 6);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_public_minus_private() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, expected, &a, &b, 2, 0, 6, 6);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_private_minus_public() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, expected, &a, &b, 2, 0, 6, 6);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_private_minus_private() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };
            let a = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);

            let name = format!("Sub: a - b {}", i);
            check_sub(&name, expected, &a, &b, 2, 0, 6, 6);
            let name = format!("SubAssign: a - b {}", i);
            check_sub_assign(&name, expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_sub_matches() {
        for i in 0..ITERATIONS {
            // Sample two random elements.
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());
            let expected = match first.checked_sub(second) {
                Some(expected) => expected,
                None => continue,
            };

            // Constant
            let first_signed = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, first);
            let second_signed = Signed::<Circuit, i64, u64, 64>::new(Mode::Constant, second);
            let candidate_a = first_signed - second_signed;
            assert_eq!(expected, candidate_a.eject_value());

            // Private
            let first_signed = Signed::<Circuit, i64, u64, 64>::new(Mode::Private, first);
            let second_signed = Signed::<Circuit, i64, u64, 64>::new(Mode::Private, second);
            let candidate_b = first_signed - second_signed;
            assert_eq!(expected, candidate_b.eject_value());
        }
    }
}
