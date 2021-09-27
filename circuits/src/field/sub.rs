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

impl<E: Environment> Sub<Self> for Field<E> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self - &other
    }
}

impl<E: Environment> Sub<&Self> for Field<E> {
    type Output = Self;

    fn sub(self, other: &Self) -> Self::Output {
        Self(self.0 + -&other.0)
    }
}

impl<E: Environment> SubAssign<Self> for Field<E> {
    fn sub_assign(&mut self, other: Self) {
        *self -= &other;
    }
}

impl<E: Environment> SubAssign<&Self> for Field<E> {
    fn sub_assign(&mut self, other: &Self) {
        self.0 += -&other.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    #[test]
    fn test_0_minus_0() {
        let zero = <Circuit as Environment>::Field::zero();

        let candidate = Field::<Circuit>::zero() - Field::zero();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::zero() - &Field::zero();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, zero) - Field::new(Mode::Public, zero);
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, zero) - Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, zero) - Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.to_value());
    }

    #[test]
    fn test_1_minus_0() {
        let zero = <Circuit as Environment>::Field::zero();
        let one = <Circuit as Environment>::Field::one();

        let candidate = Field::<Circuit>::one() - Field::zero();
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::one() - &Field::zero();
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, one) - Field::new(Mode::Public, zero);
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, one) - Field::new(Mode::Private, zero);
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, one) - Field::new(Mode::Private, zero);
        assert_eq!(one, candidate.to_value());
    }

    #[test]
    fn test_1_minus_1() {
        let zero = <Circuit as Environment>::Field::zero();
        let one = <Circuit as Environment>::Field::one();

        let candidate = Field::<Circuit>::one() - Field::one();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::one() - &Field::one();
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, one) - Field::new(Mode::Public, one);
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, one) - Field::new(Mode::Public, one);
        assert_eq!(zero, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, one) - Field::new(Mode::Private, one);
        assert_eq!(zero, candidate.to_value());
    }

    #[test]
    fn test_2_minus_1() {
        let one = <Circuit as Environment>::Field::one();
        let two = one + one;

        let candidate_two = Field::<Circuit>::one() + Field::one();
        let candidate = candidate_two - Field::one();
        assert_eq!(one, candidate.to_value());

        let candidate_two = Field::<Circuit>::one() + &Field::one();
        let candidate = candidate_two - &Field::one();
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Public, two) - Field::new(Mode::Public, one);
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, two) - Field::new(Mode::Public, one);
        assert_eq!(one, candidate.to_value());

        let candidate = Field::<Circuit>::new(Mode::Private, two) - Field::new(Mode::Private, one);
        assert_eq!(one, candidate.to_value());
    }
}
