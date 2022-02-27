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

#[derive(Debug, Default)]
pub(super) struct Transcript {
    scope: Scope,
    constants: usize,
    public: usize,
    private: usize,
    constraints: usize,
    parents: Vec<(Scope, usize, usize, usize, usize)>,
}

impl Transcript {
    pub(super) fn push(&mut self, name: &str) -> Result<(), String> {
        match name.contains('.') {
            true => Err("Scope names cannot contain periods (\".\")".to_string()),
            false => {
                // Construct the scope name.
                let scope = match self.scope.is_empty() {
                    true => name.to_string(),
                    false => format!("{}.{}", self.scope, name),
                };

                // Save the current scope members.
                self.parents.push((self.scope.clone(), self.constants, self.public, self.private, self.constraints));

                // Initialize the new scope members.
                self.scope = scope;
                self.constants = 0;
                self.public = 0;
                self.private = 0;
                self.constraints = 0;

                Ok(())
            }
        }
    }

    pub(super) fn pop(&mut self, name: &str) -> Result<(), String> {
        // Pop the current scope from the full scope.
        let (previous_scope, current_scope) = match self.scope.rsplit_once('.') {
            Some((previous_scope, current_scope)) => (previous_scope, current_scope),
            None => ("", self.scope.as_str()),
        };

        // Ensure the current scope is the last pushed scope.
        match current_scope == name {
            true => {
                if let Some((scope, constants, public, private, constraints)) = self.parents.pop() {
                    self.scope = scope;
                    self.constants = constants;
                    self.public = public;
                    self.private = private;
                    self.constraints = constraints;
                }
            }
            false => {
                return Err("Mismatching scope. Scopes must return in the reverse order they are created".to_string());
            }
        }

        Ok(())
    }

    /// Returns the current scope.
    pub(super) fn scope(&self) -> Scope {
        self.scope.clone()
    }

    /// Increments the number of constants by 1.
    pub(super) fn increment_constant(&mut self) {
        self.constants += 1;
    }

    /// Increments the number of public variables by 1.
    pub(super) fn increment_public(&mut self) {
        self.public += 1;
    }

    /// Increments the number of private variables by 1.
    pub(super) fn increment_private(&mut self) {
        self.private += 1;
    }

    /// Increments the number of constraints by 1.
    pub(super) fn increment_constraints(&mut self) {
        self.constraints += 1;
    }

    /// Returns the number of constants.
    pub(super) fn num_constants_in_scope(&self) -> usize {
        self.constants
    }

    /// Returns the number of public variables.
    pub(super) fn num_public_in_scope(&self) -> usize {
        self.public
    }

    /// Returns the number of private variables.
    pub(super) fn num_private_in_scope(&self) -> usize {
        self.private
    }

    /// Returns the number of constraints.
    pub(super) fn num_constraints_in_scope(&self) -> usize {
        self.constraints
    }
}
