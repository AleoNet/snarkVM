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

use crate::*;
use snarkvm_curves::{
    edwards_bls12::{EdwardsAffine, EdwardsParameters, Fq, Fr},
    AffineCurve,
};

use core::cell::RefCell;
use once_cell::unsync::OnceCell;
use std::rc::Rc;

thread_local! {
    static CIRCUIT: OnceCell<Circuit> = OnceCell::new();
}

#[derive(Clone)]
pub struct Circuit(Rc<RefCell<CircuitScope<Fq>>>);

impl Circuit {
    pub(super) fn cs() -> CircuitScope<<Self as Environment>::BaseField> {
        CIRCUIT.with(|circuit| {
            circuit
                .get_or_init(|| {
                    Circuit(Rc::new(RefCell::new(CircuitScope::<<Self as Environment>::BaseField>::new())))
                })
                .0
                .borrow()
                .clone()
        })
    }

    pub fn print_circuit() {
        for (scope, (a, b, c)) in Self::cs().cs.borrow().to_constraints() {
            let a = a.to_value();
            let b = b.to_value();
            let c = c.to_value();

            match (a * b) == c {
                true => eprintln!("Constraint {}:\n\t{} * {} == {}", scope, a, b, c),
                false => eprintln!("Constraint {}:\n\t{} * {} != {} (Unsatisfied)", scope, a, b, c),
            }
        }
    }

    pub fn reset_circuit() {
        CIRCUIT.with(|circuit| {
            *(*circuit.get().unwrap()).0.borrow_mut() = CircuitScope::<<Self as Environment>::BaseField>::new();
        });

        assert_eq!(0, Self::cs().num_constants());
        assert_eq!(1, Self::cs().num_public());
        assert_eq!(0, Self::cs().num_private());
        assert_eq!(0, Self::cs().num_constraints());
    }

    #[cfg(feature = "testing")]
    pub fn constraint_system_raw() -> ConstraintSystem<<Self as Environment>::BaseField> {
        Self::cs().cs.borrow().clone()
    }
}

impl Environment for Circuit {
    type Affine = EdwardsAffine;
    type AffineParameters = EdwardsParameters;
    type BaseField = Fq;
    type ScalarField = Fr;

    /// Returns the `zero` constant.
    fn zero() -> LinearCombination<Self::BaseField> {
        LinearCombination::zero()
    }

    /// Returns the `one` constant.
    fn one() -> LinearCombination<Self::BaseField> {
        LinearCombination::one()
    }

    /// Returns a new variable of the given mode and value.
    fn new_variable(mode: Mode, value: Self::BaseField) -> Variable<Self::BaseField> {
        match mode {
            Mode::Constant => Self::cs().new_constant(value),
            Mode::Public => Self::cs().new_public(value),
            Mode::Private => Self::cs().new_private(value),
        }
    }

    // /// Appends the given scope to the current environment.
    // fn push_scope(name: &str) {
    //     CIRCUIT.with(|circuit| {
    //         // Set the entire environment to the new scope.
    //         match Self::cs().push_scope(name) {
    //             Ok(()) => (),
    //             Err(error) => Self::halt(error),
    //         }
    //     })
    // }
    //
    // /// Removes the given scope from the current environment.
    // fn pop_scope(name: &str) {
    //     CIRCUIT.with(|circuit| {
    //         // Return the entire environment to the previous scope.
    //         match Self::cs().pop_scope(name) {
    //             Ok(scope) => {
    //                 scope
    //             }
    //             Err(error) => Self::halt(error),
    //         }
    //     })
    // }

    fn scoped<Fn, Output>(name: &str, logic: Fn) -> Output
    where
        Fn: FnOnce(CircuitScope<Self::BaseField>) -> Output,
    {
        CIRCUIT.with(|circuit| {
            // Set the entire environment to the new scope, and run the logic.
            let output = match Self::cs().push_scope(name) {
                Ok(scope) => {
                    *(*circuit.get().unwrap()).0.borrow_mut() = scope.clone();
                    logic(scope)
                }
                Err(error) => Self::halt(error),
            };

            // Return the entire environment to the previous scope.
            match Self::cs().pop_scope(name) {
                Ok(scope) => *(*circuit.get().unwrap()).0.borrow_mut() = scope,
                Err(error) => Self::halt(error),
            }

            output
        })
    }

    /// Adds one constraint enforcing that `(A * B) == C`.
    fn enforce<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
        C: Into<LinearCombination<Self::BaseField>>,
    {
        Self::cs().enforce(constraint)
    }

    /// Returns `true` if all constraints in the environment are satisfied.
    fn is_satisfied() -> bool {
        Self::cs().is_satisfied()
    }

    /// Returns the number of constants in the entire circuit.
    fn num_constants() -> usize {
        Self::cs().num_constants()
    }

    /// Returns the number of public variables in the entire circuit.
    fn num_public() -> usize {
        Self::cs().num_public()
    }

    /// Returns the number of private variables in the entire circuit.
    fn num_private() -> usize {
        Self::cs().num_private()
    }

    /// Returns the number of constraints in the entire circuit.
    fn num_constraints() -> usize {
        Self::cs().num_constraints()
    }

    fn affine_from_x_coordinate(x: Self::BaseField) -> Self::Affine {
        if let Some(element) = Self::Affine::from_x_coordinate(x, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return element;
            }
        }

        if let Some(element) = Self::Affine::from_x_coordinate(x, false) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return element;
            }
        }

        Self::halt(format!(
            "Failed to recover an affine group from an x-coordinate of {}",
            x
        ))
    }

    /// Halts the program from further synthesis, evaluation, and execution in the current environment.
    fn halt<S: Into<String>, T>(message: S) -> T {
        let error = message.into();
        eprintln!("{}", &error);
        panic!("{}", &error)
    }
}

#[cfg(test)]
mod tests {
    use snarkvm_circuits::{traits::Eject, BaseField, Circuit, Environment, Mode, One};
    use snarkvm_fields::One as O;

    /// Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
    fn create_example_circuit<E: Environment>() -> BaseField<E> {
        let one = <E as Environment>::BaseField::one();
        let two = one + one;

        const EXPONENT: usize = 64;

        // Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
        let mut candidate = BaseField::<E>::new(Mode::Public, one);
        let mut accumulator = BaseField::new(Mode::Private, two);
        for _ in 0..EXPONENT {
            candidate += &accumulator;
            accumulator *= BaseField::new(Mode::Private, two);
        }

        assert_eq!((accumulator - BaseField::one()).eject_value(), candidate.eject_value());
        assert_eq!(2, E::num_public());
        assert_eq!(2 * EXPONENT + 1, E::num_private());
        assert_eq!(EXPONENT, E::num_constraints());
        assert!(E::is_satisfied());

        candidate
    }

    #[test]
    fn test_print_circuit() {
        let _candidate_output = create_example_circuit::<Circuit>();
        Circuit::print_circuit()
    }
}
