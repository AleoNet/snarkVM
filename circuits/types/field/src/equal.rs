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

impl<E: Environment> Equal<Self> for Field<E> {
    type Output = Boolean<E>;

    ///
    /// Returns `true` if `self` and `other` are equal.
    ///
    /// This method costs 3 constraints.
    ///
    fn is_equal(&self, other: &Self) -> Self::Output {
        !self.is_not_equal(other)
    }
}

impl<E: Environment> Metadata<dyn Equal<Field<E>, Output = Boolean<E>>> for Field<E> {
    type Case = (CircuitType<Field<E>>, CircuitType<Field<E>>);
    type OutputType = CircuitType<Boolean<E>>;

    fn count(case: &Self::Case) -> Count {
        match case {
            (CircuitType::Constant(_), CircuitType::Constant(_)) => Count::is(1, 0, 0, 0),
            _ => Count::is(0, 0, 2, 3),
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            (CircuitType::Constant(a), CircuitType::Constant(b)) => {
                CircuitType::from(a.circuit().is_equal(&b.circuit()))
            }
            _ => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 200;

    fn check_is_equal(name: &str, expected: bool, a: &Field<Circuit>, b: &Field<Circuit>) {
        Circuit::scope(name, || {
            let candidate = a.is_equal(b);
            assert_eq!(expected, candidate.eject_value(), "({} == {})", a.eject_value(), b.eject_value());

            let case = (CircuitType::from(a), CircuitType::from(b));
            assert_count!(Equal(Field, Field) => Boolean, &case);
            assert_output_type!(Equal(Field, Field) => Boolean, case, candidate);
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        for i in 0..ITERATIONS {
            let first = UniformRand::rand(&mut test_rng());
            let second = UniformRand::rand(&mut test_rng());

            let a = Field::<Circuit>::new(mode_a, first);
            let b = Field::<Circuit>::new(mode_b, second);

            let name = format!("Equal: a == b {}", i);
            check_is_equal(&name, first == second, &a, &b);

            // Check first is equal to first.
            let a = Field::<Circuit>::new(mode_a, first);
            let b = Field::<Circuit>::new(mode_b, first);
            let name = format!("{} == {}", first, first);
            check_is_equal(&name, true, &a, &b);

            // Check second is equal to second.
            let a = Field::<Circuit>::new(mode_a, second);
            let b = Field::<Circuit>::new(mode_b, second);
            let name = format!("{} == {}", second, second);
            check_is_equal(&name, true, &a, &b);
        }
    }

    #[test]
    fn test_constant_is_equal_to_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_is_not_equal_to_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_constant_is_not_equal_to_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_public_is_equal_to_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_private_is_equal_to_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_public_is_equal_to_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_is_not_equal_to_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_is_equal_to_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_is_equal_to_private() {
        run_test(Mode::Private, Mode::Private);
    }

    #[test]
    fn test_is_eq_cases() {
        let one = <Circuit as Environment>::BaseField::one();

        // Basic `true` and `false` cases
        {
            let mut accumulator = one + one;

            for _ in 0..ITERATIONS {
                let a = Field::<Circuit>::new(Mode::Private, accumulator);
                let b = Field::<Circuit>::new(Mode::Private, accumulator);
                let is_eq = a.is_equal(&b);
                assert!(is_eq.eject_value()); // true

                let a = Field::<Circuit>::new(Mode::Private, one);
                let b = Field::<Circuit>::new(Mode::Private, accumulator);
                let is_eq = a.is_equal(&b);
                assert!(!is_eq.eject_value()); // false

                let a = Field::<Circuit>::new(Mode::Private, accumulator);
                let b = Field::<Circuit>::new(Mode::Private, accumulator - one);
                let is_eq = a.is_equal(&b);
                assert!(!is_eq.eject_value()); // false

                accumulator += one;
            }
        }
    }
}
