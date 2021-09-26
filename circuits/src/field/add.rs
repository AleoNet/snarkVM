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

impl<E: Environment> Add<Self> for Field<E> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self + &other
    }
}

impl<E: Environment> Add<&Self> for Field<E> {
    type Output = Self;

    fn add(self, other: &Self) -> Self::Output {
        Self(self.0 + other.0.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CircuitBuilder;

    const ITERATIONS: usize = 1_000;

    #[test]
    fn test_add() {
        let one = <CircuitBuilder as Environment>::Field::one();

        // Constant variables
        {
            let mut expected_sum = one;
            let mut candidate_sum = Field::<CircuitBuilder>::one();

            let scope = CircuitBuilder::span("Constant");

            for i in 0..ITERATIONS {
                expected_sum = expected_sum + &one;
                candidate_sum = candidate_sum + Field::one();
                assert_eq!(expected_sum, candidate_sum.to_value());

                assert_eq!(i + 1, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            }
        }

        // Public variables
        {
            let mut expected_sum = one;
            let mut candidate_sum = Field::<CircuitBuilder>::one();

            let scope = CircuitBuilder::span("Public");

            for i in 0..ITERATIONS {
                expected_sum = expected_sum + &one;
                candidate_sum = candidate_sum + Field::new(Mode::Public, one);
                assert_eq!(expected_sum, candidate_sum.to_value());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(i + 1, scope.num_public_in_scope());
                assert_eq!(0, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            }
        }

        // Private variables
        {
            let mut expected_sum = one;
            let mut candidate_sum = Field::<CircuitBuilder>::one();

            let scope = CircuitBuilder::span("Private");

            for i in 0..ITERATIONS {
                expected_sum = expected_sum + &one;
                candidate_sum = candidate_sum + Field::new(Mode::Private, one);
                assert_eq!(expected_sum, candidate_sum.to_value());

                assert_eq!(0, scope.num_constants_in_scope());
                assert_eq!(0, scope.num_public_in_scope());
                assert_eq!(i + 1, scope.num_private_in_scope());
                assert_eq!(0, scope.num_constraints_in_scope());
            }
        }

        println!("{:?}", CircuitBuilder::print_circuit());
    }

    #[test]
    fn test_0_plus_0() {
        let zero = <CircuitBuilder as Environment>::Field::zero();

        let candidate = Field::<CircuitBuilder>::zero() + Field::zero();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::zero() + &Field::zero();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Public, zero) + Field::new(Mode::Public, zero);
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Public, zero) + Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Private, zero) + Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.to_value());
    }

    #[test]
    fn test_0_plus_1() {
        let zero = <CircuitBuilder as Environment>::Field::zero();
        let one = <CircuitBuilder as Environment>::Field::one();

        let candidate = Field::<CircuitBuilder>::zero() + Field::one();
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::zero() + &Field::one();
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::one() + Field::zero();
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::one() + &Field::zero();
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Public, one) + Field::new(Mode::Public, zero);
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Public, one) + Field::new(Mode::Private, zero);
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Private, one) + Field::new(Mode::Private, zero);
        assert_eq!(one, candidate.to_value());
    }

    #[test]
    fn test_1_plus_1() {
        let one = <CircuitBuilder as Environment>::Field::one();
        let two = one + one;

        let candidate = Field::<CircuitBuilder>::one() + Field::one();
        assert_eq!(two, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::one() + &Field::one();
        assert_eq!(two, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Public, one) + Field::new(Mode::Public, one);
        assert_eq!(two, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Private, one) + Field::new(Mode::Public, one);
        assert_eq!(two, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Private, one) + Field::new(Mode::Private, one);
        assert_eq!(two, candidate.to_value());
    }

    #[test]
    fn test_1_plus_2() {
        let one = <CircuitBuilder as Environment>::Field::one();
        let two = one + one;
        let three = two + one;

        let candidate_two = Field::<CircuitBuilder>::one() + Field::one();
        let candidate = candidate_two + Field::one();
        assert_eq!(three, candidate.to_value());

        let candidate_two = Field::<CircuitBuilder>::one() + &Field::one();
        let candidate = candidate_two + &Field::one();
        assert_eq!(three, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Public, one) + Field::new(Mode::Public, two);
        assert_eq!(three, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Private, one) + Field::new(Mode::Public, two);
        assert_eq!(three, candidate.to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Private, one) + Field::new(Mode::Private, two);
        assert_eq!(three, candidate.to_value());
    }
}
