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

#[derive(Debug, Default)]
pub(super) struct CircuitCounter {
    scope: Scope,
    constants: usize,
    public: usize,
    private: usize,
    constraints: usize,
    parents: Vec<(Scope, usize, usize, usize, usize)>
}

impl CircuitCounter {
    pub(super) fn push(&mut self, scope: &Scope) {
        self.parents.push((self.scope.clone(), self.constants, self.public, self.private, self.constraints));

        self.scope = scope.clone();
        self.constants = 0;
        self.public = 0;
        self.private = 0;
        self.constraints = 0;
    }

    pub(super) fn pop(&mut self) {
        if let Some((scope, constants, public, private, constraints)) = self.parents.pop() {
            self.scope = scope;
            self.constants = constants;
            self.public = public;
            self.private = private;
            self.constraints = constraints;
        }
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

#[cfg(feature = "testing")]
impl Clone for CircuitCounter {
    fn clone(&self) -> Self {
        Self {
            scope: self.scope.clone(),
            constants: self.constants.clone(),
            public: self.public.clone(),
            private: self.private.clone(),
            constraints: self.constraints.clone(),
            parents: self.parents.clone()
        }
    }
}
