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

use crate::program::{Function, Identifier, Program, Template};
use snarkvm_circuits::environment::{prelude::*, Circuit};

use core::fmt;
use indexmap::IndexMap;
use std::cell::RefCell;

pub type E = Circuit;

thread_local! {
    /// The templates declared for the program.
    /// This is a map from the template name to the template.
    static TEMPLATES: RefCell<IndexMap<Identifier<AleoProgram>, Template<AleoProgram >>> = Default::default();
    /// The functions declared for the program.
    /// This is a map from the function name to the function.
    static FUNCTIONS: RefCell<IndexMap<Identifier<AleoProgram>, Function<AleoProgram >>> = Default::default();
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct AleoProgram;

impl Program for AleoProgram {
    /// Adds a new template to the program.
    ///
    /// # Errors
    /// This method will halt if the template was previously added.
    #[inline]
    fn new_template(template: Template<Self>) {
        TEMPLATES.with(|templates| {
            // Add the template to the map.
            // Ensure the template was not previously added.
            let name = template.name().clone();
            if let Some(..) = templates.borrow_mut().insert(name.clone(), template) {
                Self::halt(format!("Template \'{name}\' was previously added"))
            }
        });
    }

    /// Adds a new function to the program.
    ///
    /// # Errors
    /// This method will halt if the function was previously added.
    #[inline]
    fn new_function(function: Function<Self>) {
        FUNCTIONS.with(|functions| {
            // Add the function to the map.
            // Ensure the function was not previously added.
            let name = function.name().clone();
            if let Some(..) = functions.borrow_mut().insert(name.clone(), function) {
                Self::halt(format!("Function \'{name}\' was previously added"))
            }
        });
    }

    /// Returns `true` if the program contains a template with the given name.
    fn contains_template(name: &Identifier<Self>) -> bool {
        TEMPLATES.with(|templates| templates.borrow().contains_key(name))
    }

    /// Returns the template with the given name.
    fn get_template(name: &Identifier<Self>) -> Option<Template<Self>> {
        TEMPLATES.with(|templates| templates.borrow().get(name).cloned())
    }
}

impl Environment for AleoProgram {
    type Affine = <E as Environment>::Affine;
    type AffineParameters = <E as Environment>::AffineParameters;
    type BaseField = <E as Environment>::BaseField;
    type ScalarField = <E as Environment>::ScalarField;

    /// The maximum number of characters allowed in a string.
    const NUM_STRING_BYTES: u32 = E::NUM_STRING_BYTES;

    /// Returns the `zero` constant.
    fn zero() -> LinearCombination<Self::BaseField> {
        E::zero()
    }

    /// Returns the `one` constant.
    fn one() -> LinearCombination<Self::BaseField> {
        E::one()
    }

    /// Returns a new variable of the given mode and value.
    fn new_variable(mode: Mode, value: Self::BaseField) -> Variable<Self::BaseField> {
        E::new_variable(mode, value)
    }

    /// Returns a new witness of the given mode and value.
    fn new_witness<Fn: FnOnce() -> Output::Primitive, Output: Inject>(mode: Mode, logic: Fn) -> Output {
        E::new_witness(mode, logic)
    }

    /// Enters a new scope for the environment.
    fn scope<S: Into<String>, Fn, Output>(name: S, logic: Fn) -> Output
    where
        Fn: FnOnce() -> Output,
    {
        E::scope(name, logic)
    }

    /// Adds one constraint enforcing that `(A * B) == C`.
    fn enforce<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
        C: Into<LinearCombination<Self::BaseField>>,
    {
        E::enforce(constraint)
    }

    /// Returns `true` if all constraints in the environment are satisfied.
    fn is_satisfied() -> bool {
        E::is_satisfied()
    }

    /// Returns `true` if all constraints in the current scope are satisfied.
    fn is_satisfied_in_scope() -> bool {
        E::is_satisfied_in_scope()
    }

    /// Returns the number of constants in the entire circuit.
    fn num_constants() -> usize {
        E::num_constants()
    }

    /// Returns the number of public variables in the entire circuit.
    fn num_public() -> usize {
        E::num_public()
    }

    /// Returns the number of private variables in the entire circuit.
    fn num_private() -> usize {
        E::num_private()
    }

    /// Returns the number of constraints in the entire circuit.
    fn num_constraints() -> usize {
        E::num_constraints()
    }

    /// Returns the number of gates in the entire circuit.
    fn num_gates() -> usize {
        E::num_gates()
    }

    /// Returns the number of constants for the current scope.
    fn num_constants_in_scope() -> usize {
        E::num_constants_in_scope()
    }

    /// Returns the number of public variables for the current scope.
    fn num_public_in_scope() -> usize {
        E::num_public_in_scope()
    }

    /// Returns the number of private variables for the current scope.
    fn num_private_in_scope() -> usize {
        E::num_private_in_scope()
    }

    /// Returns the number of constraints for the current scope.
    fn num_constraints_in_scope() -> usize {
        E::num_constraints_in_scope()
    }

    /// Returns the number of gates for the current scope.
    fn num_gates_in_scope() -> usize {
        E::num_gates_in_scope()
    }

    /// A helper method to recover the y-coordinate given the x-coordinate for
    /// a twisted Edwards point, returning the affine curve point.
    fn affine_from_x_coordinate(x: Self::BaseField) -> Self::Affine {
        E::affine_from_x_coordinate(x)
    }

    /// Halts the program from further synthesis, evaluation, and execution in the current environment.
    fn halt<S: Into<String>, T>(message: S) -> T {
        E::halt(message)
    }

    /// Clears the circuit and initializes an empty environment.
    fn reset() {
        E::reset()
    }
}

impl fmt::Display for AleoProgram {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO (howardwu): Find a better way to print the circuit.
        fmt::Display::fmt(&Circuit, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits::Field;

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
        let _candidate = create_example_circuit::<AleoProgram>();
        let output = format!("{}", AleoProgram);
        println!("{}", output);
    }

    #[test]
    fn test_circuit_scope() {
        AleoProgram::scope("test_circuit_scope", || {
            assert_eq!(0, AleoProgram::num_constants());
            assert_eq!(1, AleoProgram::num_public());
            assert_eq!(0, AleoProgram::num_private());
            assert_eq!(0, AleoProgram::num_constraints());

            assert_eq!(0, AleoProgram::num_constants_in_scope());
            assert_eq!(0, AleoProgram::num_public_in_scope());
            assert_eq!(0, AleoProgram::num_private_in_scope());
            assert_eq!(0, AleoProgram::num_constraints_in_scope());
        })
    }
}
