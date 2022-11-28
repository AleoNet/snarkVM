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

use crate::LinearCombination;
use serde::{Deserialize, Serialize};
use snarkvm_fields::PrimeField;

/// Wrapper for a R1CS circuit in JSON notation.
#[derive(Serialize, Deserialize)]
pub struct CircuitJSON {
    num_constants: u64,
    num_public: u64,
    num_private: u64,
    num_constraints: u64,
    is_satisfied: bool,
    constraints: Vec<ConstraintJSON>,
}

/// Wrapper for a R1CS constraint in JSON notation.
#[derive(Serialize, Deserialize)]
pub struct ConstraintJSON {
    a: LinearCombinationJSON,
    b: LinearCombinationJSON,
    c: LinearCombinationJSON,
}

/// Wrapper for R1CS LinearCombination in JSON notation.
pub type LinearCombinationJSON = Vec<String>;

impl CircuitJSON {
    pub fn new(
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
        is_satisfied: bool,
        constraints: Vec<ConstraintJSON>,
    ) -> Self {
        Self { num_constants, num_public, num_private, num_constraints, is_satisfied, constraints }
    }
}

impl ConstraintJSON {
    pub fn new<F: PrimeField>(a: &LinearCombination<F>, b: &LinearCombination<F>, c: &LinearCombination<F>) -> Self {
        Self {
            a: ConstraintJSON::linear_combination_string(a),
            b: ConstraintJSON::linear_combination_string(b),
            c: ConstraintJSON::linear_combination_string(c),
        }
    }

    fn linear_combination_string<F: PrimeField>(lc: &LinearCombination<F>) -> LinearCombinationJSON {
        let mut lc_string = lc.to_terms().values().map(|variable| format!("{variable}")).collect::<Vec<String>>();
        lc_string.push(format!("{:?}", lc.value()));

        lc_string
    }
}
