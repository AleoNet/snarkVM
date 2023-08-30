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

pub mod verifier;
use verifier::TableExampleVerifier;

mod lookup_table;
mod verify;

use snarkvm_console_types::prelude::*;

use crate::table_example::lookup_table::LookupTable;
use std::sync::Arc;

#[derive(Clone)]
pub struct TableExample<E: Environment> {
    /// The internal TableExample verifier
    verifier: TableExampleVerifier<E>,
}

type Input<E> = Field<E>;

impl<E: Environment> TableExample<E> {
    /// Initializes a new instance of TableExample
    pub fn setup(input: &[Input<E>]) -> Result<Self> {
        // Initialize the TableExample verifier.
        let verifier = TableExampleVerifier::<E>::setup(&input)?;

        Ok(Self { verifier })
    }

    /// Returns the lookup tables.
    pub fn tables(&self) -> &Arc<Vec<LookupTable<E>>> {
        self.verifier.tables()
    }
}
