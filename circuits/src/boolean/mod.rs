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

use crate::{traits::*, Environment, LinearCombination, Mode, Variable};

use snarkvm_fields::{One as O, Zero as Z};

#[derive(Clone)]
pub struct Boolean<E: Environment>(LinearCombination<E::Field>);

impl<E: Environment> Boolean<E> {
    pub fn new(mode: Mode, value: bool) -> Self {
        let value = match value {
            true => E::Field::one(),
            false => E::Field::zero(),
        };

        let variable = E::new_variable(mode, value);

        // Ensure `a` is either 0 or 1:
        // (1 - a) * a = 0
        E::enforce(|| (E::one() - variable, variable, E::zero()));

        Self(variable.into())
    }

    pub fn to_value(&self) -> E::Field {
        self.0.to_value()
    }
}

impl<E: Environment> BooleanTrait for Boolean<E> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CircuitBuilder;

    #[test]
    fn test_new_constant() {
        let zero = <CircuitBuilder as Environment>::Field::zero();
        let one = <CircuitBuilder as Environment>::Field::one();

        assert_eq!(0, CircuitBuilder::num_constants());
        assert_eq!(1, CircuitBuilder::num_public());
        assert_eq!(0, CircuitBuilder::num_private());
        assert_eq!(0, CircuitBuilder::num_constraints());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Constant, false);
        assert_eq!(zero, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Constant, true);
        assert_eq!(one, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());

        assert_eq!(2, CircuitBuilder::num_constants());
        assert_eq!(1, CircuitBuilder::num_public());
        assert_eq!(0, CircuitBuilder::num_private());
        // assert_eq!(0, CircuitBuilder::num_constraints());
    }

    #[test]
    fn test_new_public() {
        let zero = <CircuitBuilder as Environment>::Field::zero();
        let one = <CircuitBuilder as Environment>::Field::one();

        assert_eq!(0, CircuitBuilder::num_constants());
        assert_eq!(1, CircuitBuilder::num_public());
        assert_eq!(0, CircuitBuilder::num_private());
        assert_eq!(0, CircuitBuilder::num_constraints());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Public, false);
        assert_eq!(zero, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Public, true);
        assert_eq!(one, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());

        assert_eq!(0, CircuitBuilder::num_constants());
        assert_eq!(3, CircuitBuilder::num_public());
        assert_eq!(0, CircuitBuilder::num_private());
        assert_eq!(2, CircuitBuilder::num_constraints());
    }

    #[test]
    fn test_new_private() {
        let zero = <CircuitBuilder as Environment>::Field::zero();
        let one = <CircuitBuilder as Environment>::Field::one();

        assert_eq!(0, CircuitBuilder::num_constants());
        assert_eq!(1, CircuitBuilder::num_public());
        assert_eq!(0, CircuitBuilder::num_private());
        assert_eq!(0, CircuitBuilder::num_constraints());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Private, false);
        assert_eq!(zero, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Private, true);
        assert_eq!(one, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());

        assert_eq!(0, CircuitBuilder::num_constants());
        assert_eq!(1, CircuitBuilder::num_public());
        assert_eq!(2, CircuitBuilder::num_private());
        assert_eq!(2, CircuitBuilder::num_constraints());
    }

    #[test]
    fn test_new_fail() {
        let one = <CircuitBuilder as Environment>::Field::one();
        let two = one + one;
        {
            let candidate = CircuitBuilder::new_variable(Mode::Constant, two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            CircuitBuilder::enforce(|| (CircuitBuilder::one() - candidate, candidate, CircuitBuilder::zero()));
            assert!(!CircuitBuilder::is_satisfied());
        }
        {
            let candidate = CircuitBuilder::new_variable(Mode::Public, two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            CircuitBuilder::enforce(|| (CircuitBuilder::one() - candidate, candidate, CircuitBuilder::zero()));
            assert!(!CircuitBuilder::is_satisfied());
        }
        {
            let candidate = CircuitBuilder::new_variable(Mode::Private, two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            CircuitBuilder::enforce(|| (CircuitBuilder::one() - candidate, candidate, CircuitBuilder::zero()));
            assert!(!CircuitBuilder::is_satisfied());
        }
    }
}
