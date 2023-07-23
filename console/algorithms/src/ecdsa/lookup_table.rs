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

use indexmap::IndexMap;
use snarkvm_console_types::{prelude::Environment, Field};

const DEFAULT_KEY_SIZE: usize = 2;

#[derive(Clone, Debug)]
pub struct LookupTable<E: Environment> {
    pub table: IndexMap<[Field<E>; DEFAULT_KEY_SIZE], Field<E>>,
}

impl<E: Environment> Default for LookupTable<E> {
    fn default() -> Self {
        Self { table: IndexMap::new() }
    }
}

impl<E: Environment> LookupTable<E> {
    pub fn fill(&mut self, key: [Field<E>; DEFAULT_KEY_SIZE], val: Field<E>) -> Option<Field<E>> {
        self.table.insert(key, val)
    }

    pub fn lookup(&self, key: &[Field<E>]) -> Option<(usize, &[Field<E>; 2], &Field<E>)> {
        self.table.get_full(key)
    }
}
