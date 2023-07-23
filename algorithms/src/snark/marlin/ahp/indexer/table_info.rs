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

use crate::{polycommit::sonic_pc::LabeledPolynomial, r1cs::LookupTable};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::serialize::*;

/// Information about the lookup tables in the circuit
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct TableInfo<F: PrimeField> {
    /// The lookup tables used
    pub lookup_tables: Vec<LookupTable<F>>,
    /// LDE of the first key elements of the lookup tables
    pub t_a: LabeledPolynomial<F>,
    /// LDE of the second key elements of the lookup tables
    pub t_b: LabeledPolynomial<F>,
    /// LDE of the value elements of the lookup tables
    pub t_c: LabeledPolynomial<F>,
}

impl<F: PrimeField> TableInfo<F> {
    pub fn iter(&self) -> impl IntoIterator<Item = &LabeledPolynomial<F>> {
        [&self.t_a, &self.t_b, &self.t_c].into_iter()
    }
}
