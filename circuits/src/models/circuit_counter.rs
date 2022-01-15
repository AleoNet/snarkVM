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

use crate::models::*;

use std::collections::HashMap;

#[derive(Debug, Default)]
pub(super) struct CircuitCounter {
    constants: HashMap<Scope, usize>,
    public: HashMap<Scope, usize>,
    private: HashMap<Scope, usize>,
    constraints: HashMap<Scope, usize>,
}

impl CircuitCounter {
    pub(super) fn increment_constant(&mut self, scope: &Scope) {
        match self.constants.get_mut(scope) {
            Some(counter) => *counter += 1,
            None => assert!(self.constants.insert(scope.clone(), 1).is_none()),
        }
    }

    pub(super) fn increment_public(&mut self, scope: &Scope) {
        match self.public.get_mut(scope) {
            Some(counter) => *counter += 1,
            None => assert!(self.public.insert(scope.clone(), 1).is_none()),
        }
    }

    pub(super) fn increment_private(&mut self, scope: &Scope) {
        match self.private.get_mut(scope) {
            Some(counter) => *counter += 1,
            None => assert!(self.private.insert(scope.clone(), 1).is_none()),
        }
    }

    pub(super) fn increment_constraints(&mut self, scope: &Scope) {
        match self.constraints.get_mut(scope) {
            Some(counter) => *counter += 1,
            None => assert!(self.constraints.insert(scope.clone(), 1).is_none()),
        }
    }

    pub(super) fn num_constants_in_scope(&self, scope: &Scope) -> usize {
        match self.constants.get(scope) {
            Some(counter) => *counter,
            None => 0,
        }
    }

    pub(super) fn num_public_in_scope(&self, scope: &Scope) -> usize {
        match self.public.get(scope) {
            Some(counter) => *counter,
            None => 0,
        }
    }

    pub(super) fn num_private_in_scope(&self, scope: &Scope) -> usize {
        match self.private.get(scope) {
            Some(counter) => *counter,
            None => 0,
        }
    }

    pub(super) fn num_constraints_in_scope(&self, scope: &Scope) -> usize {
        match self.constraints.get(scope) {
            Some(counter) => *counter,
            None => 0,
        }
    }
}
