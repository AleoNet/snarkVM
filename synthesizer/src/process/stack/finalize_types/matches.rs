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

use super::*;

impl<N: Network> FinalizeTypes<N> {
    /// Checks that the given operands matches the layout of the struct. The ordering of the operands matters.
    pub fn matches_struct(&self, stack: &Stack<N>, operands: &[Operand<N>], struct_: &Struct<N>) -> Result<()> {
        // Ensure the operands is not empty.
        if operands.is_empty() {
            bail!("Casting to a struct requires at least one operand")
        }

        // Retrieve the struct name.
        let struct_name = struct_.name();
        // Ensure the struct name is valid.
        ensure!(!Program::is_reserved_keyword(struct_name), "Struct name '{struct_name}' is reserved");

        // Ensure the number of struct members does not exceed the maximum.
        let num_members = operands.len();
        ensure!(num_members <= N::MAX_DATA_ENTRIES, "'{struct_name}' cannot exceed {} entries", N::MAX_DATA_ENTRIES);

        // Ensure the number of struct members match.
        let expected_num_members = struct_.members().len();
        if expected_num_members != num_members {
            bail!("'{struct_name}' expected {expected_num_members} members, found {num_members} members")
        }

        // Ensure the operand types match the struct.
        for (operand, (member_name, member_type)) in operands.iter().zip_eq(struct_.members()) {
            match operand {
                // Ensure the literal type matches the member type.
                Operand::Literal(literal) => {
                    ensure!(
                        PlaintextType::Literal(literal.to_type()) == *member_type,
                        "Struct member '{struct_name}.{member_name}' expects a {member_type}, but found '{operand}' in the operand.",
                    )
                }
                // Ensure the register type matches the member type.
                Operand::Register(register) => {
                    // Retrieve the register type.
                    let register_type = self.get_type(stack, register)?;
                    // Ensure the register type is not a record.
                    ensure!(
                        !matches!(register_type, RegisterType::Record(..)),
                        "Casting a record into a struct is illegal"
                    );
                    // Ensure the register type matches the member type.
                    ensure!(
                        register_type == RegisterType::Plaintext(*member_type),
                        "Struct member '{struct_name}.{member_name}' expects {member_type}, but found '{register_type}' in the operand '{operand}'.",
                    )
                }
                // Ensure the program ID type (address) matches the member type.
                Operand::ProgramID(..) => {
                    // Retrieve the program ID type.
                    let program_ref_type = RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address));
                    // Ensure the program ID type matches the member type.
                    ensure!(
                        program_ref_type == RegisterType::Plaintext(*member_type),
                        "Struct member '{struct_name}.{member_name}' expects {member_type}, but found '{program_ref_type}' in the operand '{operand}'.",
                    )
                }
                // Ensure the caller type (address) matches the member type.
                Operand::Caller => {
                    // Retrieve the caller type.
                    let caller_type = RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address));
                    // Ensure the caller type matches the member type.
                    ensure!(
                        caller_type == RegisterType::Plaintext(*member_type),
                        "Struct member '{struct_name}.{member_name}' expects {member_type}, but found '{caller_type}' in the operand '{operand}'.",
                    )
                }
            }
        }
        Ok(())
    }

    /// Checks that the given record matches the layout of the record type.
    /// Note: Ordering for `owner` and `gates` **does** matter, however ordering
    /// for record data does **not** matter, as long as all defined members are present.
    pub fn matches_record(&self, stack: &Stack<N>, operands: &[Operand<N>], record_type: &RecordType<N>) -> Result<()> {
        // Ensure the operands length is at least 2.
        if operands.len() < 2 {
            bail!("Casting to a record requires at least two operands")
        }

        // Retrieve the record name.
        let record_name = record_type.name();
        // Ensure the record name is valid.
        ensure!(!Program::is_reserved_keyword(record_name), "Record name '{record_name}' is reserved");

        // Ensure the first input type is an address.
        match &operands[0] {
            Operand::Literal(literal) => {
                ensure!(
                    literal.to_type() == LiteralType::Address,
                    "Casting to a record requires the first operand to be an address"
                )
            }
            Operand::Register(register) => {
                // Retrieve the register type.
                let register_type = self.get_type(stack, register)?;
                // Ensure the register type is an address.
                ensure!(
                    register_type == RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address)),
                    "Casting to a record requires the first operand to be an address"
                );
            }
            Operand::ProgramID(program_id) => {
                // Note: While the ProgramID is rendered as an address, this address is not recoverable
                // from a private key. Furthermore, programs are not allowed to own any records.
                // They must hold all necessary state in storage instead.
                bail!("Forbidden operation: Cannot cast a program ID ('{program_id}') as a record owner")
            }
            Operand::Caller => {}
        }

        // Ensure the second input type is a u64.
        match &operands[1] {
            Operand::Literal(literal) => {
                ensure!(
                    literal.to_type() == LiteralType::U64,
                    "Casting to a record requires the second operand to be a u64"
                )
            }
            Operand::Register(register) => {
                // Retrieve the register type.
                let register_type = self.get_type(stack, register)?;
                // Ensure the register type is a u64.
                ensure!(
                    register_type == RegisterType::Plaintext(PlaintextType::Literal(LiteralType::U64)),
                    "Casting to a record requires the second operand to be a u64"
                )
            }
            // These operand types are never a `u64` type.
            Operand::ProgramID(..) | Operand::Caller => {
                bail!("Casting to a record requires the second operand to be a u64")
            }
        }

        // Ensure the number of record entries does not exceed the maximum.
        let num_entries = operands.len() - 2; // Minus 2 to factor for `record.owner` and `record.gates`.
        ensure!(num_entries <= N::MAX_DATA_ENTRIES, "'{record_name}' cannot exceed {} entries", N::MAX_DATA_ENTRIES);

        // Ensure the number of record entries match.
        let expected_num_entries = record_type.entries().len();
        if expected_num_entries != num_entries {
            bail!("'{record_name}' expected {expected_num_entries} entries, found {num_entries} entries")
        }

        // Ensure the operand types match the record entry types.
        for (operand, (entry_name, entry_type)) in operands.iter().skip(2).zip_eq(record_type.entries()) {
            match entry_type {
                EntryType::Constant(plaintext_type)
                | EntryType::Public(plaintext_type)
                | EntryType::Private(plaintext_type) => {
                    match operand {
                        // Ensure the literal type matches the entry type.
                        Operand::Literal(literal) => {
                            ensure!(
                                PlaintextType::Literal(literal.to_type()) == *plaintext_type,
                                "Record entry '{record_name}.{entry_name}' expects a '{plaintext_type}', but found '{literal}' in the operand.",
                            )
                        }
                        // Ensure the register type matches the entry type.
                        Operand::Register(register) => {
                            // Retrieve the register type.
                            let register_type = self.get_type(stack, register)?;
                            // Ensure the register type is not a record.
                            ensure!(
                                !matches!(register_type, RegisterType::Record(..)),
                                "Casting a record into a record entry is illegal"
                            );
                            // Ensure the register type matches the entry type.
                            ensure!(
                                register_type == RegisterType::Plaintext(*plaintext_type),
                                "Record entry '{record_name}.{entry_name}' expects a '{plaintext_type}', but found '{register_type}' in the operand '{operand}'.",
                            )
                        }
                        // Ensure the program ID type (address) matches the member type.
                        Operand::ProgramID(..) => {
                            // Retrieve the program ID type.
                            let program_ref_type =
                                RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address));
                            // Ensure the program ID type matches the member type.
                            ensure!(
                                program_ref_type == RegisterType::Plaintext(*plaintext_type),
                                "Record entry '{record_name}.{entry_name}' expects a '{plaintext_type}', but found '{program_ref_type}' in the operand '{operand}'.",
                            )
                        }
                        // Ensure the caller type (address) matches the member type.
                        Operand::Caller => {
                            // Retrieve the caller type.
                            let caller_type = RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address));
                            // Ensure the caller type matches the member type.
                            ensure!(
                                caller_type == RegisterType::Plaintext(*plaintext_type),
                                "Record entry '{record_name}.{entry_name}' expects a '{plaintext_type}', but found '{caller_type}' in the operand '{operand}'.",
                            )
                        }
                    }
                }
            }
        }
        Ok(())
    }
}
