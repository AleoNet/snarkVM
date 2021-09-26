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

use crate::{models::*, traits::*};
use snarkvm_fields::traits::*;

use std::collections::HashMap;

#[derive(Debug)]
pub(super) struct Circuit<F: PrimeField> {
    constants: Vec<Variable<F>>,
    public: Vec<Variable<F>>,
    private: Vec<Variable<F>>,
    constraints: Vec<(LinearCombination<F>, LinearCombination<F>, LinearCombination<F>)>,
    transcript: HashMap<Variable<F>, Scope>,
    counter: CircuitCounter,
}

impl<F: PrimeField> Circuit<F> {
    pub(super) fn new() -> Self {
        Self {
            constants: Default::default(),
            public: vec![Variable::Public(0u64, F::one())],
            private: Default::default(),
            constraints: Default::default(),
            transcript: Default::default(),
            counter: Default::default(),
        }
    }

    pub(crate) fn is_satisfied(&self) -> bool {
        for (a, b, c) in &self.constraints {
            let a = a.to_value();
            let b = b.to_value();
            let c = c.to_value();

            if a * b != c {
                return false;
            }
        }
        true
    }

    /// Return the "one" input variable.
    fn one(&self) -> Variable<F> {
        self.public[0]
    }

    pub(crate) fn new_constant(&mut self, value: F, scope: Scope) -> Variable<F> {
        let variable = Variable::Constant(value);
        self.constants.push(variable);
        self.counter.increment_constant(&scope);
        self.transcript.insert(variable, scope);
        variable
    }

    pub(crate) fn new_public(&mut self, value: F, scope: Scope) -> Variable<F> {
        let variable = Variable::Public(self.public.len() as u64, value);
        self.public.push(variable);
        self.counter.increment_public(&scope);
        self.transcript.insert(variable, scope);
        variable
    }

    pub(crate) fn new_private(&mut self, value: F, scope: Scope) -> Variable<F> {
        let variable = Variable::Private(self.private.len() as u64, value);
        self.private.push(variable);
        self.counter.increment_private(&scope);
        self.transcript.insert(variable, scope);
        variable
    }

    pub(crate) fn enforce<Fn, A, B, C>(&mut self, constraint: Fn, scope: Scope)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<F>>,
        B: Into<LinearCombination<F>>,
        C: Into<LinearCombination<F>>,
    {
        let (a, b, c) = constraint();
        self.constraints.push((a.into(), b.into(), c.into()));
        self.counter.increment_constraints(&scope);
    }

    pub(crate) fn num_constants(&self) -> usize {
        self.constants.len()
    }

    pub(crate) fn num_public(&self) -> usize {
        self.public.len()
    }

    pub(crate) fn num_private(&self) -> usize {
        self.private.len()
    }

    pub(crate) fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    pub(crate) fn num_constants_in_scope(&self, scope: &Scope) -> usize {
        self.counter.num_constants_in_scope(scope)
    }

    pub(crate) fn num_public_in_scope(&self, scope: &Scope) -> usize {
        self.counter.num_public_in_scope(scope)
    }

    pub(crate) fn num_private_in_scope(&self, scope: &Scope) -> usize {
        self.counter.num_private_in_scope(scope)
    }

    pub(crate) fn num_constraints_in_scope(&self, scope: &Scope) -> usize {
        self.counter.num_constraints_in_scope(scope)
    }
}
