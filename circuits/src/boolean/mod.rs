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

        let variable = match mode {
            Mode::Constant => E::new_constant(value),
            Mode::Public => E::new_public(value),
            Mode::Private => E::new_private(value),
        };

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
    fn test_new() {
        let zero = <CircuitBuilder as Environment>::Field::zero();
        let one = <CircuitBuilder as Environment>::Field::one();

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Constant, false);
        assert_eq!(zero, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());
        // assert_eq!(0, CircuitBuilder::num_constraints());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Constant, true);
        assert_eq!(one, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());
        // assert_eq!(0, CircuitBuilder::num_constraints());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Public, false);
        assert_eq!(zero, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Public, true);
        assert_eq!(one, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Private, false);
        assert_eq!(zero, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());

        let candidate = Boolean::<CircuitBuilder>::new(Mode::Private, true);
        assert_eq!(one, candidate.to_value());
        assert!(CircuitBuilder::is_satisfied());
    }

    #[test]
    fn test_new_fail() {
        let one = <CircuitBuilder as Environment>::Field::one();
        let two = one + one;
        {
            let candidate = CircuitBuilder::new_constant(two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            CircuitBuilder::enforce(|| (CircuitBuilder::one() - candidate, candidate, CircuitBuilder::zero()));
            assert!(!CircuitBuilder::is_satisfied());
        }
        {
            let candidate = CircuitBuilder::new_public(two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            CircuitBuilder::enforce(|| (CircuitBuilder::one() - candidate, candidate, CircuitBuilder::zero()));
            assert!(!CircuitBuilder::is_satisfied());
        }
        {
            let candidate = CircuitBuilder::new_private(two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            CircuitBuilder::enforce(|| (CircuitBuilder::one() - candidate, candidate, CircuitBuilder::zero()));
            assert!(!CircuitBuilder::is_satisfied());
        }
    }
}
