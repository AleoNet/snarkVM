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

use crate::*;
use snarkvm_fields::traits::*;

use core::fmt;

pub type Scope = String;

#[derive(Debug)]
pub(super) struct R1CS<F: PrimeField> {
    constants: Vec<Variable<F>>,
    public: Vec<Variable<F>>,
    private: Vec<Variable<F>>,
    constraints: Vec<(Scope, (LinearCombination<F>, LinearCombination<F>, LinearCombination<F>))>,
    counter: Counter,
    gates: usize,
}

impl<F: PrimeField> R1CS<F> {
    /// Returns a new instance of a constraint system.
    pub(super) fn new() -> Self {
        Self {
            constants: Default::default(),
            public: vec![Variable::Public(0u64, F::one())],
            private: Default::default(),
            constraints: Default::default(),
            counter: Default::default(),
            gates: 0,
        }
    }

    /// Appends the given scope to the current environment.
    pub(super) fn push_scope(&mut self, name: &str) -> Result<(), String> {
        self.counter.push(name)
    }

    /// Removes the given scope from the current environment.
    pub(super) fn pop_scope(&mut self, name: &str) -> Result<(), String> {
        self.counter.pop(name)
    }

    /// Returns a new constant with the given value and scope.
    pub(super) fn new_constant(&mut self, value: F) -> Variable<F> {
        let variable = Variable::Constant(value);
        self.constants.push(variable);
        self.counter.increment_constant();
        variable
    }

    /// Returns a new public variable with the given value and scope.
    pub(super) fn new_public(&mut self, value: F) -> Variable<F> {
        let variable = Variable::Public(self.public.len() as u64, value);
        self.public.push(variable);
        self.counter.increment_public();
        variable
    }

    /// Returns a new private variable with the given value and scope.
    pub(super) fn new_private(&mut self, value: F) -> Variable<F> {
        let variable = Variable::Private(self.private.len() as u64, value);
        self.private.push(variable);
        self.counter.increment_private();
        variable
    }

    /// Adds one constraint enforcing that `(A * B) == C`.
    pub(super) fn enforce<Fn, A, B, C>(&mut self, constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<F>>,
        B: Into<LinearCombination<F>>,
        C: Into<LinearCombination<F>>,
    {
        let (a, b, c) = constraint();
        let (a, b, c) = (a.into(), b.into(), c.into());

        // Ensure the constraint is not comprised of constants.
        match a.is_constant() && b.is_constant() && c.is_constant() {
            true => match self.counter.scope().is_empty() {
                true => println!("Enforced constraint with constant terms: ({} * {}) =?= {}", a, b, c),
                false => println!(
                    "Enforced constraint with constant terms ({}): ({} * {}) =?= {}",
                    self.counter.scope(),
                    a,
                    b,
                    c
                ),
            },
            false => {
                let num_additions = a.num_additions() + b.num_additions() + c.num_additions();
                let num_gates = 1 + num_additions;

                self.constraints.push((self.counter.scope(), (a, b, c)));
                self.counter.increment_constraints();
                self.counter.increment_gates_by(num_gates);
                self.gates += num_gates;
            }
        }
    }

    /// Returns `true` if all constraints in the environment are satisfied.
    pub(super) fn is_satisfied(&self) -> bool {
        for (scope, (a, b, c)) in &self.constraints {
            let a = a.to_value();
            let b = b.to_value();
            let c = c.to_value();

            if a * b != c {
                eprintln!("Failed constraint at {}:\n\t({} * {}) != {}", scope, a, b, c);
                return false;
            }
        }
        true
    }

    /// Returns the number of constants in the constraint system.
    pub(super) fn num_constants(&self) -> usize {
        self.constants.len()
    }

    /// Returns the number of public variables in the constraint system.
    pub(super) fn num_public(&self) -> usize {
        self.public.len()
    }

    /// Returns the number of private variables in the constraint system.
    pub(super) fn num_private(&self) -> usize {
        self.private.len()
    }

    /// Returns the number of constraints in the constraint system.
    pub(super) fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    /// Returns the number of gates in the constraint system.
    pub(super) fn num_gates(&self) -> usize {
        self.gates
    }

    /// Returns the number of constants for the current scope.
    pub(super) fn num_constants_in_scope(&self) -> usize {
        self.counter.num_constants_in_scope()
    }

    /// Returns the number of public variables for the current scope.
    pub(super) fn num_public_in_scope(&self) -> usize {
        self.counter.num_public_in_scope()
    }

    /// Returns the number of private variables for the current scope.
    pub(super) fn num_private_in_scope(&self) -> usize {
        self.counter.num_private_in_scope()
    }

    /// Returns the number of constraints for the current scope.
    pub(super) fn num_constraints_in_scope(&self) -> usize {
        self.counter.num_constraints_in_scope()
    }

    /// Returns the number of gates for the current scope.
    pub(super) fn num_gates_in_scope(&self) -> usize {
        self.counter.num_gates_in_scope()
    }

    /// Returns the public variables in the constraint system.
    pub(super) fn to_public_variables(&self) -> &Vec<Variable<F>> {
        &self.public
    }

    /// Returns the private variables in the constraint system.
    pub(super) fn to_private_variables(&self) -> &Vec<Variable<F>> {
        &self.private
    }

    /// Returns the constraints in the constraint system.
    pub(super) fn to_constraints(
        &self,
    ) -> &Vec<(Scope, (LinearCombination<F>, LinearCombination<F>, LinearCombination<F>))> {
        &self.constraints
    }
}

impl<F: PrimeField> fmt::Display for R1CS<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut output = String::default();

        for (scope, (a, b, c)) in self.to_constraints() {
            let a = a.to_value();
            let b = b.to_value();
            let c = c.to_value();

            match (a * b) == c {
                true => output += &format!("Constraint {}:\n\t{} * {} == {}\n", scope, a, b, c),
                false => output += &format!("Constraint {}:\n\t{} * {} != {} (Unsatisfied)\n", scope, a, b, c),
            }
        }

        output += "\n";

        write!(f, "{}", output)
    }
}
