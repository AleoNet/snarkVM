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

use crate::LookupTable;
use snarkvm_fields::Field;
use std::collections::HashSet;

pub type ConstraintIndex = usize;

pub struct LookupConstraints<F: Field> {
    pub table: LookupTable<F>,
    pub indices: HashSet<ConstraintIndex>,
}

impl<F: Field> LookupConstraints<F> {
    pub fn new(table: LookupTable<F>) -> Self {
        Self { table, indices: HashSet::new() }
    }

    pub fn insert(&mut self, index: ConstraintIndex) -> bool {
        self.indices.insert(index)
    }

    pub fn lookup(&self, key: &[F]) -> Option<&F> {
        self.table.lookup(key)
    }
}
