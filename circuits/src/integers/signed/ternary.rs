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

impl<E: Environment, I: PrimitiveSignedInteger, U: PrimitiveUnsignedInteger, const SIZE: usize> Ternary
    for Signed<E, I, U, SIZE>
{
    type Boolean = Boolean<E>;
    type Output = Self;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        let mut result_bits = Vec::with_capacity(SIZE);
        for (first_bit, second_bit) in first.bits_le.iter().zip(second.bits_le.iter()) {
            result_bits.push(Ternary::ternary(condition, first_bit, second_bit));
        }
        Signed::from_bits(result_bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    fn check_ternary(
        name: &str,
        expected: i64,
        condition: Boolean<Circuit>,
        a: Signed<Circuit, i64, u64, 64>,
        b: Signed<Circuit, i64, u64, 64>,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        Circuit::scoped(name, |scope| {
            let candidate = Signed::ternary(&condition, &a, &b);
            assert_eq!(
                expected,
                candidate.eject_value(),
                "{} != {} := ({} ? {} : {})",
                expected,
                candidate.eject_value(),
                condition.eject_value(),
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
    fn test_constant_condition() {
        let first: i64 = UniformRand::rand(&mut thread_rng());
        let second: i64 = UniformRand::rand(&mut thread_rng());

        // false ? Constant : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Constant : Constant", expected, condition, a, b, 0, 0, 0, 0);

        // false ? Constant : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Constant : Public", expected, condition, a, b, 0, 0, 0, 0);

        // false ? Public : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Public : Constant", expected, condition, a, b, 0, 0, 0, 0);

        // false ? Public : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Public : Public", expected, condition, a, b, 0, 0, 0, 0);

        // false ? Public : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Public : Private", expected, condition, a, b, 0, 0, 0, 0);

        // false ? Private : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Constant, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Private : Private", expected, condition, a, b, 0, 0, 0, 0);

        // true ? Constant : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Constant : Constant", expected, condition, a, b, 0, 0, 0, 0);

        // true ? Constant : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Constant : Public", expected, condition, a, b, 0, 0, 0, 0);

        // true ? Public : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Public : Constant", expected, condition, a, b, 0, 0, 0, 0);

        // true ? Public : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Public : Public", expected, condition, a, b, 0, 0, 0, 0);

        // true ? Public : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Public : Private", expected, condition, a, b, 0, 0, 0, 0);

        // true ? Private : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Constant, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Private : Private", expected, condition, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_condition_and_constant_inputs() {
        let first: i64 = UniformRand::rand(&mut thread_rng());
        let second: i64 = UniformRand::rand(&mut thread_rng());

        // false ? Constant : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Constant : Constant", expected, condition, a, b, 0, 0, 0, 0);

        // true ? Constant : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Constant : Constant", expected, condition, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_condition_and_mixed_inputs() {
        let first: i64 = UniformRand::rand(&mut thread_rng());
        let second: i64 = UniformRand::rand(&mut thread_rng());

        // false ? Constant : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Constant : Public", expected, condition, a, b, 0, 0, 2, 2);

        // false ? Public : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Public : Constant", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Constant : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Constant : Public", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Public : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Public : Constant", expected, condition, a, b, 0, 0, 2, 2);
    }

    #[test]
    fn test_private_condition_and_constant_inputs() {
        let first: i64 = UniformRand::rand(&mut thread_rng());
        let second: i64 = UniformRand::rand(&mut thread_rng());

        // false ? Constant : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Constant : Constant", expected, condition, a, b, 0, 0, 0, 0);

        // true ? Constant : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Constant : Constant", expected, condition, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_private_condition_and_mixed_inputs() {
        let first: i64 = UniformRand::rand(&mut thread_rng());
        let second: i64 = UniformRand::rand(&mut thread_rng());

        // false ? Constant : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Constant : Public", expected, condition, a, b, 0, 0, 2, 2);

        // false ? Public : Constant
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Public : Constant", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Constant : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Constant : Public", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Public : Constant
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Public : Constant", expected, condition, a, b, 0, 0, 2, 2);
    }

    #[test]
    fn test_public_condition_and_variable_inputs() {
        let first: i64 = UniformRand::rand(&mut thread_rng());
        let second: i64 = UniformRand::rand(&mut thread_rng());

        // false ? Public : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Public : Public", expected, condition, a, b, 0, 0, 2, 2);

        // false ? Public : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Public : Private", expected, condition, a, b, 0, 0, 2, 2);

        // false ? Private : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Private : Public", expected, condition, a, b, 0, 0, 2, 2);

        // false ? Private : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Public, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Private : Private", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Public : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Public : Public", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Public : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Public : Private", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Private : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Private : Public", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Private : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Public, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Private : Private", expected, condition, a, b, 0, 0, 2, 2);
    }

    #[test]
    fn test_private_condition_and_variable_inputs() {
        let first: i64 = UniformRand::rand(&mut thread_rng());
        let second: i64 = UniformRand::rand(&mut thread_rng());

        // false ? Public : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Public : Public", expected, condition, a, b, 0, 0, 2, 2);

        // false ? Public : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Public : Private", expected, condition, a, b, 0, 0, 2, 2);

        // false ? Private : Public
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Private : Public", expected, condition, a, b, 0, 0, 2, 2);

        // false ? Private : Private
        let expected = second;
        let condition = Boolean::<Circuit>::new(Mode::Private, false);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("false ? Private : Private", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Public : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Public : Public", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Public : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Public : Private", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Private : Public
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Private : Public", expected, condition, a, b, 0, 0, 2, 2);

        // true ? Private : Private
        let expected = first;
        let condition = Boolean::<Circuit>::new(Mode::Private, true);
        let a = Signed::new(Mode::Constant, first);
        let b = Signed::new(Mode::Constant, second);
        check_ternary("true ? Private : Private", expected, condition, a, b, 0, 0, 2, 2);
    }
}
