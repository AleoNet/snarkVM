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

use crate::r1cs::LookupTable;
use snarkvm_fields::Field;
use std::collections::HashSet;

pub type ConstraintIndex = usize;

pub struct LookupConstraints<F: Field> {
    /// the lookup table to which these lookup constraints correspond
    pub table: LookupTable<F>,
    /// the indices - of the set of *all* constraints in a constraint system - which are lookup constraints
    pub indices: HashSet<ConstraintIndex>,
}

impl<F: Field> LookupConstraints<F> {
    pub fn new(table: LookupTable<F>) -> Self {
        Self { table, indices: HashSet::new() }
    }

    pub fn insert(&mut self, index: ConstraintIndex) -> bool {
        self.indices.insert(index)
    }

    pub fn lookup(&self, key: &[F]) -> Option<(usize, &[F; 2], &F)> {
        self.table.lookup(key)
    }
}
