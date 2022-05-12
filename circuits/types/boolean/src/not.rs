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
use std::rc::Rc;

impl<E: Environment> Not for Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(NOT a)`.
    fn not(self) -> Self::Output {
        (&self).not()
    }
}

impl<E: Environment> Not for &Boolean<E> {
    type Output = Boolean<E>;

    /// Returns `(NOT a)`.
    fn not(self) -> Self::Output {
        // Constant case
        if self.is_constant() {
            match self.eject_value() {
                true => Boolean(&self.0 - E::one()),
                false => Boolean(&self.0 + E::one()),
            }
        }
        // Public and private cases
        else {
            Boolean(Variable::Public(0, Rc::new(E::BaseField::one())) - &self.0)
        }
    }
}

impl<E: Environment> Metadata<dyn Not<Output = Boolean<E>>> for Boolean<E> {
    type Case = CircuitType<Boolean<E>>;
    type OutputType = CircuitType<Boolean<E>>;

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            CircuitType::Constant(constant) => CircuitType::from(constant.circuit().not()),
            _ => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_not(name: &str, expected: bool, candidate_input: Boolean<Circuit>) {
        Circuit::scope(name, || {
            let candidate_output = !&candidate_input;
            assert_eq!(expected, candidate_output.eject_value());

            let case = CircuitType::from(candidate_input);
            assert_count!(Not(Boolean) => Boolean, &case);
            assert_output_type!(Not(Boolean) => Boolean, case, candidate_output);
        });
    }

    fn run_test(mode: Mode) {
        for condition in [true, false] {
            let input = Boolean::<Circuit>::new(mode, condition);
            let name = format!("NOT {} {}", condition, mode);
            check_not(&name, !condition, input)
        }
    }

    #[test]
    fn test_not_constant() {
        run_test(Mode::Constant)
    }

    #[test]
    fn test_not_public() {
        run_test(Mode::Public)
    }

    #[test]
    fn test_not_private() {
        run_test(Mode::Private)
    }
}
