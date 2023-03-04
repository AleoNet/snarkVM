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

use super::*;

impl<N: Network> Stack<N> {
    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(&self, stack: &Stack<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of operands is correct.
        ensure!(
            input_types.len() == self.operands.len(),
            "Instruction '{}' expects {} operands, found {} operands",
            Self::opcode(),
            input_types.len(),
            self.operands.len(),
        );

        // Ensure the output type is defined in the program.
        match self.register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => bail!("Casting to literal is currently unsupported"),
            RegisterType::Plaintext(PlaintextType::Struct(struct_name)) => {
                // Retrieve the struct and ensure it is defined in the program.
                let struct_ = stack.program().get_struct(&struct_name)?;
                // Ensure the input types match the struct.
                for ((_, member_type), input_type) in struct_.members().iter().zip_eq(input_types) {
                    match input_type {
                        // Ensure the plaintext type matches the member type.
                        RegisterType::Plaintext(plaintext_type) => {
                            ensure!(
                                member_type == plaintext_type,
                                "Struct '{struct_name}' member type mismatch: expected '{member_type}', found '{plaintext_type}'"
                            )
                        }
                        // Ensure the input type cannot be a record (this is unsupported behavior).
                        RegisterType::Record(record_name) => bail!(
                            "Struct '{struct_name}' member type mismatch: expected '{member_type}', found record '{record_name}'"
                        ),
                        // Ensure the input type cannot be an external record (this is unsupported behavior).
                        RegisterType::ExternalRecord(locator) => bail!(
                            "Struct '{struct_name}' member type mismatch: expected '{member_type}', found external record '{locator}'"
                        ),
                    }
                }
            }
            RegisterType::Record(record_name) => {
                // Retrieve the record type and ensure is defined in the program.
                let record = stack.program().get_record(&record_name)?;

                // Ensure the input types length is at least 2.
                ensure!(input_types.len() >= 2, "Casting to a record requires at least two operands");
                // Ensure the first input type is an address.
                ensure!(
                    input_types[0] == RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address)),
                    "Casting to a record requires the first operand to be an address"
                );
                // Ensure the second input type is a u64.
                ensure!(
                    input_types[1] == RegisterType::Plaintext(PlaintextType::Literal(LiteralType::U64)),
                    "Casting to a record requires the second operand to be a u64"
                );

                // Ensure the input types match the record.
                for (input_type, (_, entry_type)) in input_types.iter().skip(2).zip_eq(record.entries()) {
                    match input_type {
                        // Ensure the plaintext type matches the entry type.
                        RegisterType::Plaintext(plaintext_type) => match entry_type {
                            EntryType::Constant(entry_type)
                            | EntryType::Public(entry_type)
                            | EntryType::Private(entry_type) => {
                                ensure!(
                                    entry_type == plaintext_type,
                                    "Record '{record_name}' entry type mismatch: expected '{entry_type}', found '{plaintext_type}'"
                                )
                            }
                        },
                        // Ensure the input type cannot be a record (this is unsupported behavior).
                        RegisterType::Record(record_name) => bail!(
                            "Record '{record_name}' entry type mismatch: expected '{entry_type}', found record '{record_name}'"
                        ),
                        // Ensure the input type cannot be an external record (this is unsupported behavior).
                        RegisterType::ExternalRecord(locator) => bail!(
                            "Record '{record_name}' entry type mismatch: expected '{entry_type}', found external record '{locator}'"
                        ),
                    }
                }
            }
            RegisterType::ExternalRecord(_locator) => {
                bail!("Illegal operation: Cannot cast to an external record.")
            }
        }

        Ok(vec![self.register_type])
    }
}
