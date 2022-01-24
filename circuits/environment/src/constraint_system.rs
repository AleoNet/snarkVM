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
use snarkvm_fields::traits::*;

#[derive(Debug)]
pub struct ConstraintSystem<F: PrimeField> {
    constants: Vec<Variable<F>>,
    public: Vec<Variable<F>>,
    private: Vec<Variable<F>>,
    constraints: Vec<(
        Scope,
        (LinearCombination<F>, LinearCombination<F>, LinearCombination<F>),
    )>,
}

impl<F: PrimeField> ConstraintSystem<F> {
    /// Returns a new instance of a constraint system.
    pub(super) fn new() -> Self {
        Self {
            constants: Default::default(),
            public: vec![Variable::Public(0u64, F::one())],
            private: Default::default(),
            constraints: Default::default(),
        }
    }

    /// Returns a new constant with the given value and scope.
    pub(super) fn new_constant(&mut self, value: F, scope: Scope) -> Variable<F> {
        let variable = Variable::Constant(value);
        self.constants.push(variable);
        variable
    }

    /// Returns a new public variable with the given value and scope.
    pub(super) fn new_public(&mut self, value: F, scope: Scope) -> Variable<F> {
        let variable = Variable::Public(self.public.len() as u64, value);
        self.public.push(variable);
        variable
    }

    /// Returns a new private variable with the given value and scope.
    pub(super) fn new_private(&mut self, value: F, scope: Scope) -> Variable<F> {
        let variable = Variable::Private(self.private.len() as u64, value);
        self.private.push(variable);
        variable
    }

    /// Adds one constraint enforcing that `(A * B) == C`.
    pub(super) fn enforce(&mut self, a: LinearCombination<F>, b: LinearCombination<F>, c: LinearCombination<F>, scope: Scope) {
        // Ensure the constraint is not comprised of constants.
        if !(a.is_constant() && b.is_constant() && c.is_constant()) {
            self.constraints.push((scope.clone(), (a, b, c)));
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
    ) -> &Vec<(
        Scope,
        (LinearCombination<F>, LinearCombination<F>, LinearCombination<F>),
    )> {
        &self.constraints
    }
}

#[cfg(feature = "testing")]
impl<F: PrimeField> Clone for ConstraintSystem<F> {
    fn clone(&self) -> Self {
        Self {
            constants: self.constants.clone(),
            public: self.public.clone(),
            private: self.private.clone(),
            constraints: self.constraints.clone(),
        }
    }
}
