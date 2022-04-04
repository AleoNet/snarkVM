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

use crate::{helpers::Constraint, *};
use snarkvm_curves::{
    edwards_bls12::{EdwardsAffine, EdwardsParameters, Fq, Fr},
    AffineCurve,
};

use core::{cell::RefCell, fmt};
use std::rc::Rc;

thread_local! {
    pub(super) static CIRCUIT: Rc<RefCell<R1CS<Fq>>> = Rc::new(RefCell::new(R1CS::<Fq>::new()));
    pub(super) static IN_WITNESS: Rc<RefCell<bool>> = Rc::new(RefCell::new(false));
    pub(super) static ZERO: LinearCombination<Fq> = LinearCombination::zero();
    pub(super) static ONE: LinearCombination<Fq> = LinearCombination::one();
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Circuit;

impl Environment for Circuit {
    type Affine = EdwardsAffine;
    type AffineParameters = EdwardsParameters;
    type BaseField = Fq;
    type ScalarField = Fr;

    /// The maximum number of characters allowed in a string.
    const NUM_STRING_BYTES: u32 = u8::MAX as u32;

    /// Returns the `zero` constant.
    fn zero() -> LinearCombination<Self::BaseField> {
        ZERO.with(|zero| zero.clone())
    }

    /// Returns the `one` constant.
    fn one() -> LinearCombination<Self::BaseField> {
        ONE.with(|one| one.clone())
    }

    /// Returns a new variable of the given mode and value.
    fn new_variable(mode: Mode, value: Self::BaseField) -> Variable<Self::BaseField> {
        IN_WITNESS.with(|in_witness| {
            // Ensure we are not in witness mode.
            if !(*(**in_witness).borrow()) {
                CIRCUIT.with(|circuit| match mode {
                    Mode::Constant => (**circuit).borrow_mut().new_constant(value),
                    Mode::Public => (**circuit).borrow_mut().new_public(value),
                    Mode::Private => (**circuit).borrow_mut().new_private(value),
                })
            } else {
                Self::halt("Tried to initialize a new variable in witness mode")
            }
        })
    }

    /// Returns a new witness of the given mode and value.
    fn new_witness<Fn: FnOnce() -> Output::Primitive, Output: Inject>(mode: Mode, logic: Fn) -> Output {
        IN_WITNESS.with(|in_witness| {
            // Set the entire environment to witness mode.
            *(**in_witness).borrow_mut() = true;

            // Run the logic.
            let output = logic();

            // Return the entire environment from witness mode.
            *(**in_witness).borrow_mut() = false;

            Inject::new(mode, output)
        })
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

    /// Enters a new scope for the environment.
    fn scope<S: Into<String>, Fn, Output>(name: S, logic: Fn) -> Output
    where
        Fn: FnOnce() -> Output,
    {
        IN_WITNESS.with(|in_witness| {
            // Ensure we are not in witness mode.
            if !(*(**in_witness).borrow()) {
                CIRCUIT.with(|circuit| {
                    // Set the entire environment to the new scope.
                    let name = name.into();
                    if let Err(error) = (**circuit).borrow_mut().push_scope(&name) {
                        Self::halt(error)
                    }

                    // Run the logic.
                    let output = logic();

                    // Return the entire environment to the previous scope.
                    if let Err(error) = (**circuit).borrow_mut().pop_scope(name) {
                        Self::halt(error)
                    }

                    output
                })
            } else {
                Self::halt("Tried to initialize a new scope in witness mode")
            }
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
        IN_WITNESS.with(|in_witness| {
            // Ensure we are not in witness mode.
            if !(*(**in_witness).borrow()) {
                CIRCUIT.with(|circuit| {
                    let (a, b, c) = constraint();
                    let (a, b, c) = (a.into(), b.into(), c.into());

                    // Ensure the constraint is not comprised of constants.
                    match a.is_constant() && b.is_constant() && c.is_constant() {
                        true => {
                            // Disabled for now until better control handling for this can be defined (using scope).

                            // match self.counter.scope().is_empty() {
                            //     true => println!("Enforced constraint with constant terms: ({} * {}) =?= {}", a, b, c),
                            //     false => println!(
                            //         "Enforced constraint with constant terms ({}): ({} * {}) =?= {}",
                            //         self.counter.scope(), a, b, c
                            //     ),
                            // }
                        }
                        false => {
                            // Construct the constraint object.
                            let constraint = Constraint((**circuit).borrow().scope(), a, b, c);
                            // Append the constraint.
                            (**circuit).borrow_mut().enforce(constraint)
                        }
                    }
                });
            }
        })
    }

    /// Returns `true` if all constraints in the environment are satisfied.
    fn is_satisfied() -> bool {
        CIRCUIT.with(|circuit| (**circuit).borrow().is_satisfied())
    }

    /// Returns `true` if all constraints in the current scope are satisfied.
    fn is_satisfied_in_scope() -> bool {
        CIRCUIT.with(|circuit| (**circuit).borrow().is_satisfied_in_scope())
    }

    /// Returns the number of constants in the entire circuit.
    fn num_constants() -> usize {
        CIRCUIT.with(|circuit| (**circuit).borrow().num_constants())
    }

    /// Returns the number of public variables in the entire circuit.
    fn num_public() -> usize {
        CIRCUIT.with(|circuit| (**circuit).borrow().num_public())
    }

    /// Returns the number of private variables in the entire circuit.
    fn num_private() -> usize {
        CIRCUIT.with(|circuit| (**circuit).borrow().num_private())
    }

    /// Returns the number of constraints in the entire circuit.
    fn num_constraints() -> usize {
        CIRCUIT.with(|circuit| (**circuit).borrow().num_constraints())
    }

    /// Returns the number of gates in the entire circuit.
    fn num_gates() -> usize {
        CIRCUIT.with(|circuit| (**circuit).borrow().num_gates())
    }

    /// Returns the number of constants for the current scope.
    fn num_constants_in_scope() -> usize {
        CIRCUIT.with(|circuit| (**circuit).borrow().num_constants_in_scope())
    }

    /// Returns the number of public variables for the current scope.
    fn num_public_in_scope() -> usize {
        CIRCUIT.with(|circuit| (**circuit).borrow().num_public_in_scope())
    }

    /// Returns the number of private variables for the current scope.
    fn num_private_in_scope() -> usize {
        CIRCUIT.with(|circuit| (**circuit).borrow().num_private_in_scope())
    }

    /// Returns the number of constraints for the current scope.
    fn num_constraints_in_scope() -> usize {
        CIRCUIT.with(|circuit| (**circuit).borrow().num_constraints_in_scope())
    }

    /// Returns the number of gates for the current scope.
    fn num_gates_in_scope() -> usize {
        CIRCUIT.with(|circuit| (**circuit).borrow().num_gates_in_scope())
    }

    /// A helper method to recover the y-coordinate given the x-coordinate for
    /// a twisted Edwards point, returning the affine curve point.
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

        Self::halt(format!("Failed to recover an affine group from an x-coordinate of {}", x))
    }

    /// Halts the program from further synthesis, evaluation, and execution in the current environment.
    fn halt<S: Into<String>, T>(message: S) -> T {
        let error = message.into();
        // eprintln!("{}", &error);
        panic!("{}", &error)
    }

    /// Clears the circuit and initializes an empty environment.
    fn reset() {
        CIRCUIT.with(|circuit| {
            *(**circuit).borrow_mut() = R1CS::<<Self as Environment>::BaseField>::new();
            assert_eq!(0, (**circuit).borrow().num_constants());
            assert_eq!(1, (**circuit).borrow().num_public());
            assert_eq!(0, (**circuit).borrow().num_private());
            assert_eq!(0, (**circuit).borrow().num_constraints());
        });
    }
}

impl fmt::Display for Circuit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        CIRCUIT.with(|circuit| write!(f, "{}", (**circuit).borrow()))
    }
}

#[cfg(test)]
mod tests {
    use snarkvm_circuits::prelude::*;

    /// Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
    fn create_example_circuit<E: Environment>() -> Field<E> {
        let one = <E as Environment>::BaseField::one();
        let two = one + one;

        const EXPONENT: usize = 64;

        // Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
        let mut candidate = Field::<E>::new(Mode::Public, one);
        let mut accumulator = Field::new(Mode::Private, two);
        for _ in 0..EXPONENT {
            candidate += &accumulator;
            accumulator *= Field::new(Mode::Private, two);
        }

        assert_eq!((accumulator - Field::one()).eject_value(), candidate.eject_value());
        assert_eq!(2, E::num_public());
        assert_eq!(2 * EXPONENT + 1, E::num_private());
        assert_eq!(EXPONENT, E::num_constraints());
        assert!(E::is_satisfied());

        candidate
    }

    #[test]
    fn test_print_circuit() {
        let _candidate = create_example_circuit::<Circuit>();
        let output = format!("{}", Circuit);
        println!("{}", output);
    }

    #[test]
    fn test_circuit_scope() {
        Circuit::scope("test_circuit_scope", || {
            assert_eq!(0, Circuit::num_constants());
            assert_eq!(1, Circuit::num_public());
            assert_eq!(0, Circuit::num_private());
            assert_eq!(0, Circuit::num_constraints());

            assert_eq!(0, Circuit::num_constants_in_scope());
            assert_eq!(0, Circuit::num_public_in_scope());
            assert_eq!(0, Circuit::num_private_in_scope());
            assert_eq!(0, Circuit::num_constraints_in_scope());
        })
    }
}
