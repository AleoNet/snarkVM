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
use snarkvm_fields::PrimeField;

use core::cell::RefCell;
use std::rc::Rc;

pub type Scope = String;

#[derive(Clone)]
pub struct CircuitScope<F: PrimeField> {
    pub(super) cs: Rc<RefCell<ConstraintSystem<F>>>,
    scope: Scope,
    counter: Rc<RefCell<CircuitCounter>>,
}

impl<F: PrimeField> CircuitScope<F> {
    pub(super) fn new() -> Self {
        Self {
            cs: Rc::new(RefCell::new(ConstraintSystem::new())),
            scope: Default::default(),
            counter: Rc::new(RefCell::new(Default::default())),
        }
    }

    /// Appends the given scope to the current environment.
    pub(super) fn push_scope(&self, name: &str) -> Result<Self, String> {
        match name.contains(".") {
            true => Err("Scope names cannot contain periods (\".\")".to_string()),
            false => {
                let scope = match self.scope.is_empty() {
                    true => format!("{}", name),
                    false => format!("{}.{}", self.scope, name),
                };

                self.counter.borrow_mut().push(&scope);

                Ok(Self {
                    cs: self.cs.clone(),
                    scope,
                    counter: self.counter.clone(),
                })
            }
        }
    }

    /// Removes the given scope from the current environment.
    pub(super) fn pop_scope(&self, name: &str) -> Result<Self, String> {
        // Pop the current scope from the entire scope.
        let (previous_scope, current_scope) = match self.scope.rsplit_once('.') {
            Some((previous_scope, current_scope)) => (previous_scope, current_scope),
            None => ("", self.scope.as_str()),
        };

        self.counter.borrow_mut().pop();

        // Ensure the current scope is the last pushed scope.
        match current_scope == name {
            true => Ok(Self {
                cs: self.cs.clone(),
                scope: previous_scope.to_string(),
                counter: self.counter.clone(),
            }),
            false => Err("Mismatching scope. Scopes must return in the reverse order they are created".to_string()),
        }
    }

    /// Returns a new constant in the current scope with the given value.
    pub(super) fn new_constant(&mut self, value: F) -> Variable<F> {
        let variable = self.cs.borrow_mut().new_constant(value, self.scope.clone());
        self.counter.borrow_mut().increment_constant();
        variable
    }

    /// Returns a new public variable in the current scope with the given value.
    pub(super) fn new_public(&mut self, value: F) -> Variable<F> {
        let variable = self.cs.borrow_mut().new_public(value, self.scope.clone());
        self.counter.borrow_mut().increment_public();
        variable
    }

    /// Returns a new private variable in the current scope with the given value.
    pub(super) fn new_private(&mut self, value: F) -> Variable<F> {
        let variable = self.cs.borrow_mut().new_private(value, self.scope.clone());
        self.counter.borrow_mut().increment_private();
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

        if !(a.is_constant() && b.is_constant() && c.is_constant()) {
            self.cs.borrow_mut().enforce(a, b, c, self.scope.clone());
            self.counter.borrow_mut().increment_constraints();
        }
    }

    /// Returns `true` if all constraints in the environment are satisfied.
    pub fn is_satisfied(&self) -> bool {
        self.cs.borrow().is_satisfied()
    }

    /// Returns the number of constants in the entire circuit.
    pub(super) fn num_constants(&self) -> usize {
        self.cs.borrow().num_constants()
    }

    /// Returns the number of public variables in the entire circuit.
    pub(super) fn num_public(&self) -> usize {
        self.cs.borrow().num_public()
    }

    /// Returns the number of private variables in the entire circuit.
    pub(super) fn num_private(&self) -> usize {
        self.cs.borrow().num_private()
    }

    /// Returns the number of constraints in the entire circuit.
    pub(super) fn num_constraints(&self) -> usize {
        self.cs.borrow().num_constraints()
    }

    /// Returns the number of constants for the given scope.
    pub fn num_constants_in_scope(&self) -> usize {
        self.counter.borrow().num_constants_in_scope()
    }

    /// Returns the number of public variables for the given scope.
    pub fn num_public_in_scope(&self) -> usize {
        self.counter.borrow().num_public_in_scope()
    }

    /// Returns the number of private variables for the given scope.
    pub fn num_private_in_scope(&self) -> usize {
        self.counter.borrow().num_private_in_scope()
    }

    /// Returns the number of constraints for the given scope.
    pub fn num_constraints_in_scope(&self) -> usize {
        self.counter.borrow().num_constraints_in_scope()
    }
}
