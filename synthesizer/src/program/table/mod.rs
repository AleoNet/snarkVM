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

use console::{
    network::prelude::*,
    program::{Field, Identifier, Literal, LiteralType, PlaintextType},
};
use snarkvm_r1cs::LookupTable;

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
    ) -> Result<Self> {
        // TODO (d0cd): Consider moving validation logic elsewhere.
        let input_types = inputs.iter().map(|input| input.type_()).collect::<Vec<_>>();
        let output_types = outputs.iter().map(|output| output.type_()).collect::<Vec<_>>();

        // Temporarily restrict tables to 3 inputs and 0 outputs.
        if input_types.len() != 3 {
            bail!("Tables are temporarily restricted to have exactly 3 inputs.")
        }
        if !output_types.is_empty() {
            bail!("Tables are temporarily restricted to have exactly 0 outputs.")
        }

        // For each entry, check that the input and output types match the table.
        for entry in entries.iter() {
            if entry.inputs().len() != input_types.len() {
                bail!("A table entry must have {} inputs, but found {}.", input_types.len(), entry.inputs().len());
            }
            if entry.outputs().len() != output_types.len() {
                bail!("A table entry must have {} outputs, but found {}.", output_types.len(), entry.outputs().len());
            }
            for (input, input_type) in entry.inputs().iter().zip_eq(input_types.iter()) {
                // Temporarily requires that input types are field elements.
                if !matches!(input_type, PlaintextType::Literal(LiteralType::Field)) {
                    bail!("Input types are temporarily restricted to field elements.")
                }
                if !matches!(PlaintextType::<N>::from(input.to_type()), input_type) {
                    bail!("Expected input with type {}, but found {}.", input_type, input.to_type());
                }
            }
            for (output, output_type) in entry.outputs().iter().zip_eq(output_types.iter()) {
                // Temporarily requires that output types are field elements.
                if !matches!(output_type, PlaintextType::Literal(LiteralType::Field)) {
                    bail!("Output types are temporarily restricted to field elements.")
                }
                if !matches!(PlaintextType::<N>::from(output.to_type()), output_type) {
                    bail!("Expected output with type {}, but found {}.", output_type, output.to_type());
                }
            }
        }
        Ok(Self { name, inputs, outputs, entries })
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

impl<N: Network> Table<N> {
    pub fn into_lookup_table<A: circuit::Aleo<Network = N, BaseField = N::Field>>(
        &self,
    ) -> LookupTable<<A as circuit::Environment>::BaseField> {
        let mut lookup_table = LookupTable::default();
        for entry in self.entries() {
            let inputs = entry.inputs();
            let in1 = match inputs[0] {
                Literal::Field(ref value) => value,
                _ => unreachable!(),
            };
            let in2 = match inputs[1] {
                Literal::Field(ref value) => value,
                _ => unreachable!(),
            };
            let in3 = match inputs[2] {
                Literal::Field(ref value) => value,
                _ => unreachable!(),
            };
            lookup_table.fill([**in1, **in2], **in3);
        }
        lookup_table
    }
}

impl<N: Network> TypeName for Table<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "table"
    }
}
