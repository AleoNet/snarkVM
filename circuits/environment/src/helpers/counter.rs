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
use snarkvm_fields::PrimeField;

#[derive(Debug, Default)]
pub(crate) struct Counter<F: PrimeField> {
    scope: Scope,
    constraints: Vec<Constraint<F>>,
    constants: u64,
    public: u64,
    private: u64,
    gates: u64,
    parents: Vec<(Scope, Vec<Constraint<F>>, u64, u64, u64, u64)>,
}

impl<F: PrimeField> Counter<F> {
    /// Saves and switches from the current scope to a new scope.
    pub(crate) fn push<S: Into<String>>(&mut self, name: S) -> Result<(), String> {
        let name = name.into();
        match name.contains('.') {
            true => Err("Scope names cannot contain periods (\".\")".to_string()),
            false => {
                // Construct the scope name.
                let scope = match self.scope.is_empty() {
                    true => name,
                    false => format!("{}.{}", self.scope, name),
                };

                // Save the current scope members.
                self.parents.push((
                    self.scope.clone(),
                    self.constraints.clone(),
                    self.constants,
                    self.public,
                    self.private,
                    self.gates,
                ));

                // Initialize the new scope members.
                self.scope = scope;
                self.constraints = Default::default();
                self.constants = 0;
                self.public = 0;
                self.private = 0;
                self.gates = 0;

                Ok(())
            }
        }
    }

    /// Discards the current scope, reverting to the previous scope.
    pub(crate) fn pop<S: Into<String>>(&mut self, name: S) -> Result<(), String> {
        // Pop the current scope from the full scope.
        let (_previous_scope, current_scope) = match self.scope.rsplit_once('.') {
            Some((previous_scope, current_scope)) => (previous_scope, current_scope),
            None => ("", self.scope.as_str()),
        };

        // Ensure the current scope is the last pushed scope.
        match current_scope == name.into() {
            true => {
                if let Some((scope, constraints, constants, public, private, gates)) = self.parents.pop() {
                    self.scope = scope;
                    self.constraints = constraints;
                    self.constants = constants;
                    self.public = public;
                    self.private = private;
                    self.gates = gates;
                }
            }
            false => {
                return Err("Mismatching scope. Scopes must return in the reverse order they are created".to_string());
            }
        }

        Ok(())
    }

    /// Increments the number of constraints by 1.
    pub(crate) fn add_constraint(&mut self, constraint: Constraint<F>) {
        self.gates += constraint.num_gates();
        self.constraints.push(constraint);
    }

    /// Returns `true` if all constraints in the scope are satisfied.
    pub(crate) fn is_satisfied_in_scope(&self) -> bool {
        self.constraints.iter().all(|constraint| constraint.is_satisfied())
    }

    /// Returns the current scope.
    pub(crate) fn scope(&self) -> Scope {
        self.scope.clone()
    }

    /// Increments the number of constants by 1.
    pub(crate) fn increment_constant(&mut self) {
        self.constants += 1;
    }

    /// Increments the number of public variables by 1.
    pub(crate) fn increment_public(&mut self) {
        self.public += 1;
    }

    /// Increments the number of private variables by 1.
    pub(crate) fn increment_private(&mut self) {
        self.private += 1;
    }

    /// Returns the number of constants in scope in scope.
    pub(crate) fn num_constants_in_scope(&self) -> u64 {
        self.constants
    }

    /// Returns the number of public variables in scope.
    pub(crate) fn num_public_in_scope(&self) -> u64 {
        self.public
    }

    /// Returns the number of private variables in scope.
    pub(crate) fn num_private_in_scope(&self) -> u64 {
        self.private
    }

    /// Returns the number of constraints in scope.
    pub(crate) fn num_constraints_in_scope(&self) -> u64 {
        self.constraints.len() as u64
    }

    /// Returns the number of gates in scope.
    pub(crate) fn num_gates_in_scope(&self) -> u64 {
        self.gates
    }
}
