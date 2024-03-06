// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{LinearCombination, Variable};
use serde::{Deserialize, Serialize};
use snarkvm_fields::PrimeField;

/// Wrapper for a R1CS circuit in JSON notation.
#[derive(Serialize, Deserialize, Default)]
pub struct CircuitJSON {
    num_constants: u64,
    num_public: u64,
    num_private: u64,
    num_constraints: u64,
    is_satisfied: bool,
    constraints: Vec<ConstraintJSON>,
}

/// Wrapper for a R1CS constraint in JSON notation.
#[derive(Serialize, Deserialize, Default)]
pub struct ConstraintJSON {
    a: LinearCombinationJSON,
    b: LinearCombinationJSON,
    c: LinearCombinationJSON,
}

/// Wrapper for R1CS LinearCombination in JSON notation.
pub type LinearCombinationJSON = Vec<(String, String)>;

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
            a: ConstraintJSON::linear_combination_json(a),
            b: ConstraintJSON::linear_combination_json(b),
            c: ConstraintJSON::linear_combination_json(c),
        }
    }

    fn variable_json<F: PrimeField>(v: &Variable<F>) -> String {
        match v {
            Variable::Constant(val) => format!("c{}", val),
            Variable::Public(idx) => format!("x{:?}", idx),
            Variable::Private(idx) => format!("w{:?}", idx),
        }
    }

    fn linear_combination_json<F: PrimeField>(lc: &LinearCombination<F>) -> LinearCombinationJSON {
        let mut lc_json = lc
            .to_terms()
            .iter()
            .map(|(key, value)| (Self::variable_json(key), format!("{value}")))
            .collect::<Vec<(String, String)>>();
        //lc_string.push(format!("{:?}", lc.value()));
        if !lc.to_constant().is_zero() {
            lc_json.push((String::from("ONE"), format!("{}", lc.to_constant())));
        }
        lc_json
    }
}
