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

use crate::{prelude::*, *};
use snarkvm_fields::PrimeField;

#[derive(Clone, Debug)]
pub(crate) struct Constraint<F: PrimeField>(
    pub(crate) Scope,
    pub(crate) LinearCombination<F>,
    pub(crate) LinearCombination<F>,
    pub(crate) LinearCombination<F>,
);

impl<F: PrimeField> Constraint<F> {
    /// Returns the number of gates consumed by this constraint.
    pub(crate) fn num_gates(&self) -> u64 {
        let (a, b, c) = (&self.1, &self.2, &self.3);
        1 + a.num_additions() + b.num_additions() + c.num_additions()
    }

    /// Returns `true` if the constraint is satisfied.
    pub(crate) fn is_satisfied(&self) -> bool {
        let (scope, a, b, c) = (&self.0, &self.1, &self.2, &self.3);
        let a = a.value();
        let b = b.value();
        let c = c.value();

        match a * b == c {
            true => true,
            false => {
                eprintln!("Failed constraint at {scope}:\n\t({a} * {b}) != {c}");
                false
            }
        }
    }

    /// Returns a reference to the terms `(a, b, c)`.
    pub(crate) fn to_terms(&self) -> (&LinearCombination<F>, &LinearCombination<F>, &LinearCombination<F>) {
        (&self.1, &self.2, &self.3)
    }
}

impl<F: PrimeField> Display for Constraint<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (scope, a, b, c) = (&self.0, &self.1, &self.2, &self.3);
        let a = a.value();
        let b = b.value();
        let c = c.value();

        match (a * b) == c {
            true => write!(f, "Constraint {scope}:\n\t{a} * {b} == {c}\n"),
            false => write!(f, "Constraint {scope}:\n\t{a} * {b} != {c} (Unsatisfied)\n"),
        }
    }
}
