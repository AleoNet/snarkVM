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

use crate::errors::SynthesisError;

use indexmap::IndexMap;
use snarkvm_fields::Field;
use snarkvm_utilities::serialize::*;

#[derive(Clone)]
pub struct LookupTable<F: Field> {
    arity: usize,
    table: IndexMap<Vec<F>, F>,
}

impl<F: Field> LookupTable<F> {
    pub fn new(arity: usize) -> Self {
        Self { arity, table: IndexMap::new() }
    }

    pub fn fill(&mut self, key: Vec<F>, val: F) -> Result<Option<F>, SynthesisError> {
        if key.len() != self.arity {
            Err(SynthesisError::LookupKeyWrongLength(key.len(), self.arity))
        } else {
            Ok(self.table.insert(key, val))
        }
    }

    pub fn lookup(&self, key: &[F]) -> Option<&F> {
        self.table.get(key)
    }

    pub fn arity(&self) -> usize {
        self.arity
    }
}
