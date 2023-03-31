// Copyright (C) 2019-2023 Aleo Systems Inc.
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

mod entry;
use entry::*;

mod input;
use input::*;

mod output;
use output::*;

mod bytes;
mod parse;

use console::{network::prelude::*, program::Identifier};

#[derive(Clone, PartialEq, Eq)]
pub struct Table<N: Network> {
    /// The name of the table.
    name: Identifier<N>,
    /// The input columns of the table.
    inputs: Vec<TableInput<N>>,
    /// The output columns of the table.
    outputs: Vec<TableOutput<N>>,
    /// The entries of the table.
    entries: Vec<Entry<N>>,
}

impl<N: Network> Table<N> {
    /// Initializes a new mapping with the given name, key statement, and value statement.
    pub fn new(
        name: Identifier<N>,
        inputs: Vec<TableInput<N>>,
        outputs: Vec<TableOutput<N>>,
        entries: Vec<Entry<N>>,
    ) -> Self {
        Self { name, inputs, outputs, entries }
    }

    /// Returns the name of the table.
    pub const fn name(&self) -> &Identifier<N> {
        &self.name
    }

    /// Returns the inputs columns of the table.
    pub fn inputs(&self) -> &[TableInput<N>] {
        &self.inputs
    }

    /// Returns the output columns of the table.
    pub fn outputs(&self) -> &[TableOutput<N>] {
        &self.outputs
    }

    /// Returns the entries of the table.
    pub fn entries(&self) -> &[Entry<N>] {
        &self.entries
    }
}

impl<N: Network> TypeName for Table<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "table"
    }
}
