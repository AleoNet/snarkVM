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

#[cfg(all(test, console))]
use crate::Verify;
use snarkvm_algorithms::r1cs::LookupTable;
use snarkvm_circuit_types::prelude::*;

pub struct TableExampleVerifier<E: Environment> {
    tables: Vec<LookupTable<E::BaseField>>,
}

impl<E: Environment> TableExampleVerifier<E> {
    /// Returns the tables
    pub(crate) fn tables(&self) -> &Vec<LookupTable<E::BaseField>> {
        &self.tables
    }
}

#[cfg(console)]
impl<E: Environment> Inject for TableExampleVerifier<E> {
    type Primitive = console::TableExample<E::Network>;

    /// Initializes a new instance of a TableExample circuit
    fn new(_mode: Mode, table_example: Self::Primitive) -> Self {
        let mut tables: Vec<LookupTable<E::BaseField>> = vec![];
        Self { tables }
    }
}
