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

mod verify;

use crate::table_example::lookup_table::LookupTable;
use snarkvm_console_types::prelude::*;

use std::sync::Arc;

#[derive(Clone)]
pub struct TableExampleVerifier<E: Environment> {
    tables: Arc<Vec<LookupTable<E>>>,
}

type Input<E> = Field<E>;

impl<E: Environment> TableExampleVerifier<E> {
    /// Initializes a new instance of TableExample
    pub fn setup(input: &[Input<E>]) -> Result<Self> {
        let key_0 = input[0];
        let key_1 = input[1];
        let val = input[2];

        let mut tables = vec![];
        let mut lookup_table = LookupTable::default();
        let lookup_value = [key_0, key_1];
        lookup_table.fill(lookup_value, val);
        tables.push(lookup_table);

        Ok(Self { tables: Arc::new(tables) })
    }

    /// Returns the tables
    pub fn tables(&self) -> &Arc<Vec<LookupTable<E>>> {
        &self.tables
    }
}
