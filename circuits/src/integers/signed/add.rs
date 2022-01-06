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
use num_traits::CheckedAdd;
use snarkvm_fields::PrimeField;

impl<E: Environment, I, const SIZE: usize> Add<Self> for Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedAdd,
    bool: AsPrimitive<I>,
{
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

impl<E: Environment, I, const SIZE: usize> Add<&Self> for Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedAdd,
    bool: AsPrimitive<I>,
{
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        // Determine the variable mode.
        let mode = match self.is_constant() && other.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        };

        //// This swap reduces the number of constants by one.
        //let (this, that) = match other.is_constant() {
        //    true => (&self, other),
        //    false => (other, &self),
        //};
        let (this, that) = (self, other);

        // Directly compute the sum, check for overflow.
        // TODO (@pranav) Do we want a better error recovery mechanism?
        let value = this
            .eject_value()
            .checked_add(&that.eject_value())
            .expect("Signed integer overflow");

        if mode.is_constant() {
            return Signed::new(mode, value);
        }

        //let result = Signed::new(mode, value);
        return Signed::new(mode, value);
    }
}

impl<E: Environment, I, const SIZE: usize> Add<Signed<E, I, SIZE>> for &Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedAdd,
    bool: AsPrimitive<I>,
{
    type Output = Signed<E, I, SIZE>;

    fn add(self, other: Signed<E, I, SIZE>) -> Self::Output {
        (*self).clone() + other
    }
}

impl<E: Environment, I, const SIZE: usize> Add<&Signed<E, I, SIZE>> for &Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedAdd,
    bool: AsPrimitive<I>,
{
    type Output = Signed<E, I, SIZE>;

    fn add(self, other: &Signed<E, I, SIZE>) -> Self::Output {
        (*self).clone() + other
    }
}

impl<E: Environment, I, const SIZE: usize> AddAssign<Self> for Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedAdd,
    bool: AsPrimitive<I>,
{
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<E: Environment, I, const SIZE: usize> AddAssign<&Self> for Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedAdd,
    bool: AsPrimitive<I>,
{
    fn add_assign(&mut self, other: &Self) {
        *self = self.clone() + other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 100;

    fn check_add(
        name: &str,
        expected: i64,
        a: &Signed<Circuit, i64, 64>,
        b: &Signed<Circuit, i64, 64>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate = a + b;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} + {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            assert_eq!(num_constants, scope.num_constants_in_scope());
            assert_eq!(num_public, scope.num_public_in_scope());
            assert_eq!(num_private, scope.num_private_in_scope());
            assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    fn check_add_assign(
        name: &str,
        expected: i64,
        a: &Signed<Circuit, i64, 64>,
        b: &Signed<Circuit, i64, 64>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let mut candidate = a.clone();
            candidate += b;
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} + {})",
                expected,
                candidate.eject_value(),
                a.eject_value(),
                b.eject_value()
            );

            assert_eq!(num_constants, scope.num_constants_in_scope());
            assert_eq!(num_public, scope.num_public_in_scope());
            assert_eq!(num_private, scope.num_private_in_scope());
            assert_eq!(num_constraints, scope.num_constraints_in_scope());
            assert!(Circuit::is_satisfied());
        });
    }

    #[test]
    fn test_constant_plus_constant() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_add(second) {
                Some(valid) => valid,
                None => continue,
            };
            let a = Signed::<Circuit, i64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Constant, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, expected, &a, &b, 4, 0, 0, 0);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, expected, &a, &b, 4, 0, 0, 0);
        }
    }

    #[test]
    fn test_constant_plus_public() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_add(second) {
                Some(valid) => valid,
                None => continue,
            };
            let a = Signed::<Circuit, i64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Public, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, expected, &a, &b, 2, 0, 3, 3);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_public_plus_constant() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_add(second) {
                Some(valid) => valid,
                None => continue,
            };
            let a = Signed::<Circuit, i64, 64>::new(Mode::Public, first);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Constant, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, expected, &a, &b, 2, 0, 3, 3);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_constant_plus_private() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_add(second) {
                Some(valid) => valid,
                None => continue,
            };
            let a = Signed::<Circuit, i64, 64>::new(Mode::Constant, first);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Private, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, expected, &a, &b, 2, 0, 3, 3);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_private_plus_constant() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_add(second) {
                Some(valid) => valid,
                None => continue,
            };
            let a = Signed::<Circuit, i64, 64>::new(Mode::Private, first);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Constant, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, expected, &a, &b, 2, 0, 3, 3);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, expected, &a, &b, 2, 0, 3, 3);
        }
    }

    #[test]
    fn test_public_plus_public() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_add(second) {
                Some(valid) => valid,
                None => continue,
            };
            let a = Signed::<Circuit, i64, 64>::new(Mode::Public, first);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Public, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, expected, &a, &b, 2, 0, 6, 6);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_public_plus_private() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_add(second) {
                Some(valid) => valid,
                None => continue,
            };
            let a = Signed::<Circuit, i64, 64>::new(Mode::Public, first);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Private, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, expected, &a, &b, 2, 0, 6, 6);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_private_plus_public() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_add(second) {
                Some(valid) => valid,
                None => continue,
            };
            let a = Signed::<Circuit, i64, 64>::new(Mode::Private, first);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Public, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, expected, &a, &b, 2, 0, 6, 6);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, expected, &a, &b, 2, 0, 6, 6);
        }
    }

    #[test]
    fn test_private_plus_private() {
        for i in 0..ITERATIONS {
            let first: i64 = UniformRand::rand(&mut thread_rng());
            let second: i64 = UniformRand::rand(&mut thread_rng());

            let expected = match first.checked_add(second) {
                Some(valid) => valid,
                None => continue,
            };
            let a = Signed::<Circuit, i64, 64>::new(Mode::Private, first);
            let b = Signed::<Circuit, i64, 64>::new(Mode::Private, second);

            let name = format!("Add: a + b {}", i);
            check_add(&name, expected, &a, &b, 2, 0, 6, 6);
            let name = format!("AddAssign: a + b {}", i);
            check_add_assign(&name, expected, &a, &b, 2, 0, 6, 6);
        }
    }
}
