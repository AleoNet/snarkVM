// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{Mode, *};

use core::{cell::RefCell, fmt};
use std::{fmt::Formatter, iter, rc::Rc};

use serde::{Deserialize, Serialize};

type Field = <console::MainnetV0 as console::Environment>::Field;

thread_local! {
    pub(super) static TRANSCRIPT: Rc<RefCell<ConstraintTranscript>> = Rc::new(RefCell::new(ConstraintTranscript::new()));
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct FormalCircuit;

impl Environment for FormalCircuit {
    type Affine = <Circuit as Environment>::Affine;
    type BaseField = Field;
    type Network = <Circuit as Environment>::Network;
    type ScalarField = <Circuit as Environment>::ScalarField;

    /// Returns the `zero` constant.
    fn zero() -> LinearCombination<Self::BaseField> {
        Circuit::zero()
    }

    /// Returns the `one` constant.
    fn one() -> LinearCombination<Self::BaseField> {
        Circuit::one()
    }

    /// Returns a new variable of the given mode and value.
    fn new_variable(mode: Mode, value: Self::BaseField) -> Variable<Self::BaseField> {
        Circuit::new_variable(mode, value)
    }

    /// Returns a new witness of the given mode and value.
    fn new_witness<Fn: FnOnce() -> Output::Primitive, Output: Inject>(mode: Mode, logic: Fn) -> Output {
        Circuit::new_witness(mode, logic)
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
        Circuit::scope(name, logic)
    }

    /// Adds one constraint enforcing that `(A * B) == C`.
    fn enforce<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
        C: Into<LinearCombination<Self::BaseField>>,
    {
        let (a, b, c) = constraint();
        let a = a.into();
        let b = b.into();
        let c = c.into();
        // Log constraint if all terms are not constant.
        if !a.is_constant() || !b.is_constant() || !c.is_constant() {
            let constraint_json = ConstraintJSON::new(&a, &b, &c);
            Self::log(serde_json::to_string_pretty(&constraint_json).unwrap().to_string());
        }
        Circuit::enforce(|| (a, b, c))
    }

    /// Returns `true` if all constraints in the environment are satisfied.
    fn is_satisfied() -> bool {
        Circuit::is_satisfied()
    }

    /// Returns `true` if all constraints in the current scope are satisfied.
    fn is_satisfied_in_scope() -> bool {
        Circuit::is_satisfied_in_scope()
    }

    /// Returns the number of constants in the entire circuit.
    fn num_constants() -> u64 {
        Circuit::num_constants()
    }

    /// Returns the number of public variables in the entire circuit.
    fn num_public() -> u64 {
        Circuit::num_public()
    }

    /// Returns the number of private variables in the entire circuit.
    fn num_private() -> u64 {
        Circuit::num_private()
    }

    /// Returns the number of constraints in the entire circuit.
    fn num_constraints() -> u64 {
        Circuit::num_constraints()
    }

    /// Returns the number of nonzeros in the entire circuit.
    fn num_nonzeros() -> (u64, u64, u64) {
        Circuit::num_nonzeros()
    }

    /// Returns the number of constants for the current scope.
    fn num_constants_in_scope() -> u64 {
        Circuit::num_constants_in_scope()
    }

    /// Returns the number of public variables for the current scope.
    fn num_public_in_scope() -> u64 {
        Circuit::num_public_in_scope()
    }

    /// Returns the number of private variables for the current scope.
    fn num_private_in_scope() -> u64 {
        Circuit::num_private_in_scope()
    }

    /// Returns the number of constraints for the current scope.
    fn num_constraints_in_scope() -> u64 {
        Circuit::num_constants_in_scope()
    }

    /// Returns the number of nonzeros for the current scope.
    fn num_nonzeros_in_scope() -> (u64, u64, u64) {
        Circuit::num_nonzeros_in_scope()
    }

    /// Halts the program from further synthesis, evaluation, and execution in the current environment.
    fn halt<S: Into<String>, T>(message: S) -> T {
        Circuit::halt(message)
    }

    /// Store the R1CS circuit in the current environment.
    fn inject_r1cs(r1cs: R1CS<Self::BaseField>) {
        Circuit::inject_r1cs(r1cs)
    }

    /// Returns the R1CS circuit, resetting the circuit.
    fn eject_r1cs_and_reset() -> R1CS<Self::BaseField> {
        Circuit::eject_r1cs_and_reset()
    }

    /// Returns the R1CS assignment of the circuit, resetting the circuit.
    fn eject_assignment_and_reset() -> Assignment<<Self::Network as console::Environment>::Field> {
        Circuit::eject_assignment_and_reset()
    }

    /// Clears the circuit and initializes an empty environment.
    fn reset() {
        Circuit::reset()
    }

    /// Returns the constraint limit for the circuit, if one exists.
    fn get_constraint_limit() -> Option<u64> {
        None //CONSTRAINT_LIMIT.with(|current_limit| current_limit.get())
    }

    /// Sets the constraint limit for the circuit.
    fn set_constraint_limit(limit: Option<u64>) {
        //CONSTRAINT_LIMIT.with(|current_limit| current_limit.replace(limit));
    }
}

#[derive(Serialize, Deserialize)]
pub struct ScopedEntry {
    pub depth: usize,
    pub message: String,
}

#[derive(Serialize, Deserialize, Default)]
pub struct ConstraintTranscript {
    pub scope_index: usize,
    pub entries: Vec<ScopedEntry>,
}

impl ConstraintTranscript {
    fn new() -> Self {
        Self { scope_index: 0, entries: Vec::new() }
    }

    fn push(&mut self) {
        self.scope_index = self.scope_index.saturating_add(1usize)
    }

    fn pop(&mut self) {
        self.scope_index = self.scope_index.saturating_sub(1usize)
    }

    fn log(&mut self, message: String) {
        self.entries.push(ScopedEntry { depth: self.scope_index, message })
    }

    fn clear(&mut self) -> Self {
        core::mem::take(self)
    }
}

impl fmt::Display for ConstraintTranscript {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut space = iter::repeat(" ");
        for entry in &self.entries {
            let indent: String = (&mut space).take(entry.depth).collect();
            write!(f, "{indent}{}", entry.message)?;
        }
        Ok(())
    }
}

impl Transcribe for FormalCircuit {
    type Transcript = ConstraintTranscript;

    /// Pushes a scope onto the transcript.
    fn push() {
        TRANSCRIPT.with(|transcript| (**transcript).borrow_mut().push())
    }

    /// Pops the current scope off the transcript.
    fn pop() {
        TRANSCRIPT.with(|transcript| (**transcript).borrow_mut().pop())
    }

    /// Log a message into the transcript.
    fn log(message: String) {
        TRANSCRIPT.with(|transcript| (**transcript).borrow_mut().log(message))
    }

    /// Clears and returns the accumulated transcript.
    fn clear() -> Self::Transcript {
        TRANSCRIPT.with(|transcript| (**transcript).borrow_mut().clear())
    }
}

impl fmt::Display for FormalCircuit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        CIRCUIT.with(|circuit| write!(f, "{}", (*circuit).borrow()))
    }
}

#[cfg(test)]
mod tests {
    use snarkvm_circuit::prelude::*;

    /// Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
    fn create_example_circuit<E: Environment>() -> Field<E> {
        let one = snarkvm_console_types::Field::<E::Network>::one();
        let two = one + one;

        const EXPONENT: u64 = 64;

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
        let _candidate = create_example_circuit::<FormalCircuit>();
        let output = format!("{FormalCircuit}");
        println!("{output}");
    }

    #[test]
    fn test_circuit_scope() {
        FormalCircuit::scope("test_circuit_scope", || {
            assert_eq!(0, FormalCircuit::num_constants());
            assert_eq!(1, FormalCircuit::num_public());
            assert_eq!(0, FormalCircuit::num_private());
            assert_eq!(0, FormalCircuit::num_constraints());

            assert_eq!(0, FormalCircuit::num_constants_in_scope());
            assert_eq!(0, FormalCircuit::num_public_in_scope());
            assert_eq!(0, FormalCircuit::num_private_in_scope());
            assert_eq!(0, FormalCircuit::num_constraints_in_scope());
        })
    }
}
