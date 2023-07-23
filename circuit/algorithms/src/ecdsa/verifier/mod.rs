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

pub struct ECDSAVerifier<E: Environment> {
    tables: Vec<LookupTable<E::BaseField>>,
}

impl<E: Environment> ECDSAVerifier<E> {
    /// Returns the tables
    pub(crate) fn tables(&self) -> &Vec<LookupTable<E::BaseField>> {
        &self.tables
    }
}

#[cfg(console)]
impl<E: Environment> Inject for ECDSAVerifier<E> {
    type Primitive = console::ECDSA<E::Network>;

    /// Initializes a new instance of a ECDSA circuit
    fn new(_mode: Mode, ecdsa: Self::Primitive) -> Self {
        let mut tables: Vec<LookupTable<E::BaseField>> = vec![];
        // TODO: how to fill tables based on ecdsa.tables()
        // for table in ecdsa.tables().iter() {
        //     let mut new_table = IndexMap::new();
        //     for entry in table.table.iter() {
        //         let key_0 = Field::constant(entry.0[0]);
        //         let key_1 = Field::constant(entry.0[1]);
        //         let value = Field::constant(*entry.1);
        //         new_table.insert([key_0, key_1], value);
        //     }
        //     tables.push(LookupTable::<E::BaseField>{table: new_table});
        // }
        // let tables = Vec::constant(new_tables);
        // let tables = Vec::constant(ecdsa.tables().iter().cloned().collect());
        // Example from BHP:
        // let random_base = Vec::constant(bhp.random_base().iter().copied().collect());
        Self { tables }
    }
}
