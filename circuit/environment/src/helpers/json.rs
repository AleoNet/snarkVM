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
use serde::{Deserialize, Serialize};

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
    a: String,
    b: String,
    c: String,
}

impl CircuitJSON {
    pub fn new(
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
        is_satisfied: bool,
        constraints: Vec<ConstraintJSON>,
    ) -> Self {
        CircuitJSON { num_constants, num_public, num_private, num_constraints, is_satisfied, constraints }
    }
}

impl ConstraintJSON {
    pub fn new(a: String, b: String, c: String) -> Self {
        ConstraintJSON { a, b, c }
    }
}
