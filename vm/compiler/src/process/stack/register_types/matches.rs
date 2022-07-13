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

use crate::process::stack::*;

impl<N: Network> RegisterTypes<N> {
    /// Checks that the given operands matches the layout of the interface. The ordering of the operands matters.
    pub fn matches_interface<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N, A>,
        operands: &[Operand<N>],
        interface: &Interface<N>,
    ) -> Result<()> {
        // Ensure the operands is not empty.
        if operands.is_empty() {
            bail!("Casting to an interface requires at least one operand")
        }
        // Ensure the operand types match the interface.
        for (operand, (_, member_type)) in operands.iter().zip(interface.members()) {
            match operand {
                // Ensure the literal type matches the member type.
                Operand::Literal(literal) => {
                    ensure!(
                        PlaintextType::Literal(literal.to_type()) == *member_type,
                        "Interface '{}' expects {member_type}, operand is '{literal}'.",
                        interface.name()
                    )
                }
                // Ensure the register type matches the member type.
                Operand::Register(register) => {
                    // Retrieve the register type.
                    let register_type = self.get_type(stack, register)?;
                    // Ensure the register type is not a record.
                    ensure!(
                        !matches!(register_type, RegisterType::Record(..)),
                        "Casting a record into an interface is illegal"
                    );
                    // Ensure the register type matches the member type.
                    ensure!(
                        register_type == RegisterType::Plaintext(*member_type),
                        "Interface '{}' expects {member_type}, operand is '{register_type}'.",
                        interface.name()
                    )
                }
            }
        }
        Ok(())
    }

    /// Checks that the given record matches the layout of the record type.
    /// Note: Ordering for `owner` and `balance` **does** matter, however ordering
    /// for record data does **not** matter, as long as all defined members are present.
    pub fn matches_record<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N, A>,
        operands: &[Operand<N>],
        record_type: &RecordType<N>,
    ) -> Result<()> {
        // Ensure the operands length is at least 2.
        if operands.len() < 2 {
            bail!("Casting to a record requires at least two operands")
        }

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
        }

        // Ensure the operand types match the record entry types.
        for (operand, (_, entry_type)) in operands.iter().skip(2).zip(record_type.entries()) {
            match entry_type {
                EntryType::Constant(plaintext_type)
                | EntryType::Public(plaintext_type)
                | EntryType::Private(plaintext_type) => {
                    match operand {
                        // Ensure the literal type matches the entry type.
                        Operand::Literal(literal) => {
                            ensure!(
                                PlaintextType::Literal(literal.to_type()) == *plaintext_type,
                                "Record '{}' expects {plaintext_type}, operand is '{literal}'.",
                                record_type.name()
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
                                "Record '{}' expects {plaintext_type}, operand is '{register_type}'.",
                                record_type.name()
                            )
                        }
                    }
                }
            }
        }
        Ok(())
    }
}
