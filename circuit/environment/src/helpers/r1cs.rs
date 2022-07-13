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

use crate::{
    helpers::{Constraint, Counter},
    prelude::*,
};
use snarkvm_fields::PrimeField;

use std::rc::Rc;

pub type Scope = String;

#[derive(Debug)]
pub struct R1CS<F: PrimeField> {
    constants: Vec<Variable<F>>,
    public: Vec<Variable<F>>,
    private: Vec<Variable<F>>,
    constraints: Vec<Constraint<F>>,
    counter: Counter<F>,
    gates: u64,
}

impl<F: PrimeField> R1CS<F> {
    /// Returns a new instance of a constraint system.
    pub(crate) fn new() -> Self {
        Self {
            constants: Default::default(),
            public: vec![Variable::Public(0u64, Rc::new(F::one()))],
            private: Default::default(),
            constraints: Default::default(),
            counter: Default::default(),
            gates: 0,
        }
    }

    /// Appends the given scope to the current environment.
    pub(crate) fn push_scope<S: Into<String>>(&mut self, name: S) -> Result<(), String> {
        self.counter.push(name)
    }

    /// Removes the given scope from the current environment.
    pub(crate) fn pop_scope<S: Into<String>>(&mut self, name: S) -> Result<(), String> {
        self.counter.pop(name)
    }

    /// Returns a new constant with the given value and scope.
    pub(crate) fn new_constant(&mut self, value: F) -> Variable<F> {
        let variable = Variable::Constant(Rc::new(value));
        self.constants.push(variable.clone());
        self.counter.increment_constant();
        variable
    }

    /// Returns a new public variable with the given value and scope.
    pub(crate) fn new_public(&mut self, value: F) -> Variable<F> {
        let variable = Variable::Public(self.public.len() as u64, Rc::new(value));
        self.public.push(variable.clone());
        self.counter.increment_public();
        variable
    }

    /// Returns a new private variable with the given value and scope.
    pub(crate) fn new_private(&mut self, value: F) -> Variable<F> {
        let variable = Variable::Private(self.private.len() as u64, Rc::new(value));
        self.private.push(variable.clone());
        self.counter.increment_private();
        variable
    }

    /// Adds one constraint enforcing that `(A * B) == C`.
    pub(crate) fn enforce(&mut self, constraint: Constraint<F>) {
        self.gates += constraint.num_gates();
        self.constraints.push(constraint.clone());
        self.counter.add_constraint(constraint);
    }

    /// Returns `true` if all constraints in the environment are satisfied.
    pub(crate) fn is_satisfied(&self) -> bool {
        self.constraints.iter().all(|constraint| constraint.is_satisfied())
    }

    /// Returns `true` if all constraints in the current scope are satisfied.
    pub(crate) fn is_satisfied_in_scope(&self) -> bool {
        self.counter.is_satisfied_in_scope()
    }

    /// Returns the current scope.
    pub(crate) fn scope(&self) -> Scope {
        self.counter.scope()
    }

    /// Returns the number of constants in the constraint system.
    pub(crate) fn num_constants(&self) -> u64 {
        self.constants.len() as u64
    }

    /// Returns the number of public variables in the constraint system.
    pub(crate) fn num_public(&self) -> u64 {
        self.public.len() as u64
    }

    /// Returns the number of private variables in the constraint system.
    pub(crate) fn num_private(&self) -> u64 {
        self.private.len() as u64
    }

    /// Returns the number of constraints in the constraint system.
    pub(crate) fn num_constraints(&self) -> u64 {
        self.constraints.len() as u64
    }

    /// Returns the number of gates in the constraint system.
    pub(crate) fn num_gates(&self) -> u64 {
        self.gates
    }

    /// Returns the number of constants for the current scope.
    pub(crate) fn num_constants_in_scope(&self) -> u64 {
        self.counter.num_constants_in_scope()
    }

    /// Returns the number of public variables for the current scope.
    pub(crate) fn num_public_in_scope(&self) -> u64 {
        self.counter.num_public_in_scope()
    }

    /// Returns the number of private variables for the current scope.
    pub(crate) fn num_private_in_scope(&self) -> u64 {
        self.counter.num_private_in_scope()
    }

    /// Returns the number of constraints for the current scope.
    pub(crate) fn num_constraints_in_scope(&self) -> u64 {
        self.counter.num_constraints_in_scope()
    }

    /// Returns the number of gates for the current scope.
    pub(crate) fn num_gates_in_scope(&self) -> u64 {
        self.counter.num_gates_in_scope()
    }

    /// Returns the public variables in the constraint system.
    pub(crate) fn to_public_variables(&self) -> &Vec<Variable<F>> {
        &self.public
    }

    /// Returns the private variables in the constraint system.
    pub(crate) fn to_private_variables(&self) -> &Vec<Variable<F>> {
        &self.private
    }

    /// Returns the constraints in the constraint system.
    pub(crate) fn to_constraints(&self) -> &Vec<Constraint<F>> {
        &self.constraints
    }
}

impl<F: PrimeField> Display for R1CS<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut output = String::default();
        for constraint in self.to_constraints() {
            output += &constraint.to_string();
        }
        output += "\n";

        write!(f, "{}", output)
    }
}
