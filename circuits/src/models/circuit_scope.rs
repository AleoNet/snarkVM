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
use snarkvm_fields::PrimeField;

use std::{cell::RefCell, rc::Rc};

pub type Scope = String;

#[derive(Clone)]
pub struct CircuitScope<F: PrimeField> {
    pub(super) cs: Rc<RefCell<ConstraintSystem<F>>>,
    scope: Scope,
    previous: Option<Scope>,
}

impl<F: PrimeField> CircuitScope<F> {
    pub(super) fn new(circuit: Rc<RefCell<ConstraintSystem<F>>>, scope: Scope, previous: Option<Scope>) -> Self {
        Self { cs: circuit, scope, previous }
    }

    pub(super) fn new_scope(self, name: &str) -> Self {
        Self { cs: self.cs.clone(), scope: format!("{}/{}", self.scope, name), previous: Some(self.scope) }
    }

    pub(crate) fn new_constant(&mut self, value: F) -> Variable<F> {
        self.cs.borrow_mut().new_constant(value, self.scope.clone())
    }

    pub(crate) fn new_public(&mut self, value: F) -> Variable<F> {
        self.cs.borrow_mut().new_public(value, self.scope.clone())
    }

    pub(crate) fn new_private(&mut self, value: F) -> Variable<F> {
        self.cs.borrow_mut().new_private(value, self.scope.clone())
    }

    pub(crate) fn enforce<Fn, A, B, C>(&mut self, constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<F>>,
        B: Into<LinearCombination<F>>,
        C: Into<LinearCombination<F>>,
    {
        self.cs.borrow_mut().enforce(constraint, self.scope.clone());
    }

    pub(crate) fn is_satisfied(&self) -> bool {
        self.cs.borrow().is_satisfied()
    }

    pub(super) fn num_constants(&self) -> usize {
        self.cs.borrow().num_constants()
    }

    pub(super) fn num_public(&self) -> usize {
        self.cs.borrow().num_public()
    }

    pub(super) fn num_private(&self) -> usize {
        self.cs.borrow().num_private()
    }

    pub(super) fn num_constraints(&self) -> usize {
        self.cs.borrow().num_constraints()
    }

    pub fn num_constants_in_scope(&self) -> usize {
        self.cs.borrow().num_constants_in_scope(&self.scope)
    }

    pub fn num_public_in_scope(&self) -> usize {
        self.cs.borrow().num_public_in_scope(&self.scope)
    }

    pub fn num_private_in_scope(&self) -> usize {
        self.cs.borrow().num_private_in_scope(&self.scope)
    }

    pub fn num_constraints_in_scope(&self) -> usize {
        self.cs.borrow().num_constraints_in_scope(&self.scope)
    }
}

// impl<F: PrimeField> Drop for CircuitScope<F> {
//     #[inline]
//     fn drop(&mut self) {
//         println!("I AM IN DROP {:?} {:?}", self.scope, self.previous);
//         // if let Some(scope) = &self.previous {
//         //     println!("I AM DROPPING {:?} {:?}", self.scope, self.previous);
//         //
//         //     let prev = (*self).circuit.borrow_mut().pop_scope();
//         //     (*self).scope = (prev).clone();
//         //     (*self).previous = None;
//         //
//         //     // CB.with(|cb| {
//         //     //     (*cb.get().unwrap().borrow_mut()).0.scope = (*scope).clone();
//         //     //     // (*cb.get().unwrap().borrow_mut()).0.scope = (*scope).clone();
//         //     // });
//         // }
//     }
// }
