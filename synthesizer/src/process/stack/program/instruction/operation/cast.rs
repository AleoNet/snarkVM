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
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate_cast<A: circuit::Aleo<Network = N>>(
        &self,
        cast: &Cast<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> = cast.operands().iter().map(|operand| registers.load(self, operand)).try_collect()?;

        match cast.register_type() {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => bail!("Casting to literal is currently unsupported"),
            RegisterType::Plaintext(PlaintextType::Struct(struct_name)) => {
                // Ensure the operands is not empty.
                ensure!(!inputs.is_empty(), "Casting to a struct requires at least one operand");

                // Retrieve the struct and ensure it is defined in the program.
                let struct_ = self.program().get_struct(&struct_name)?;

                // Initialize the struct members.
                let mut members = IndexMap::new();
                for (member, (member_name, member_type)) in inputs.iter().zip_eq(struct_.members()) {
                    // Compute the register type.
                    let register_type = RegisterType::Plaintext(*member_type);
                    // Retrieve the plaintext value from the entry.
                    let plaintext = match member {
                        Value::Plaintext(plaintext) => {
                            // Ensure the member matches the register type.
                            self.matches_register_type(&Value::Plaintext(plaintext.clone()), &register_type)?;
                            // Output the plaintext.
                            plaintext.clone()
                        }
                        // Ensure the struct member is not a record.
                        Value::Record(..) => bail!("Casting a record into a struct member is illegal"),
                    };
                    // Append the member to the struct members.
                    members.insert(*member_name, plaintext);
                }

                // Construct the struct.
                let struct_ = Plaintext::Struct(members, Default::default());
                // Store the struct.
                registers.store(self, &cast.destinations()[0], Value::Plaintext(struct_))
            }
            RegisterType::Record(record_name) => {
                // Ensure the operands length is at least 2.
                ensure!(inputs.len() >= 2, "Casting to a record requires at least two operands");

                // Retrieve the struct and ensure it is defined in the program.
                let record_type = self.program().get_record(&record_name)?;

                // Initialize the record owner.
                let owner: Owner<N, Plaintext<N>> = match &inputs[0] {
                    // Ensure the entry is an address.
                    Value::Plaintext(Plaintext::Literal(Literal::Address(owner), ..)) => {
                        match record_type.owner().is_public() {
                            true => Owner::Public(*owner),
                            false => Owner::Private(Plaintext::Literal(Literal::Address(*owner), Default::default())),
                        }
                    }
                    _ => bail!("Invalid record 'owner'"),
                };

                // Initialize the record gates.
                let gates: Balance<N, Plaintext<N>> = match &inputs[1] {
                    // Ensure the entry is a u64.
                    Value::Plaintext(Plaintext::Literal(Literal::U64(gates), ..)) => {
                        // Ensure the gates is less than or equal to 2^52.
                        ensure!(
                            gates.to_bits_le()[52..].iter().all(|bit| !bit),
                            "Attempted to initialize an invalid Aleo balance (in gates)"
                        );
                        // Construct the record gates.
                        match record_type.gates().is_public() {
                            true => Balance::Public(*gates),
                            false => Balance::Private(Plaintext::Literal(Literal::U64(*gates), Default::default())),
                        }
                    }
                    _ => bail!("Invalid record 'gates'"),
                };

                // Initialize the record entries.
                let mut entries = IndexMap::new();
                for (entry, (entry_name, entry_type)) in inputs.iter().skip(2).zip_eq(record_type.entries()) {
                    // Compute the register type.
                    let register_type = RegisterType::from(ValueType::from(*entry_type));
                    // Retrieve the plaintext value from the entry.
                    let plaintext = match entry {
                        Value::Plaintext(plaintext) => {
                            // Ensure the entry matches the register type.
                            self.matches_register_type(&Value::Plaintext(plaintext.clone()), &register_type)?;
                            // Output the plaintext.
                            plaintext.clone()
                        }
                        // Ensure the record entry is not a record.
                        Value::Record(..) => bail!("Casting a record into a record entry is illegal"),
                    };
                    // Append the entry to the record entries.
                    match entry_type {
                        EntryType::Constant(..) => entries.insert(*entry_name, Entry::Constant(plaintext)),
                        EntryType::Public(..) => entries.insert(*entry_name, Entry::Public(plaintext)),
                        EntryType::Private(..) => entries.insert(*entry_name, Entry::Private(plaintext)),
                    };
                }

                // Prepare the index as a field element.
                let index = Field::from_u64(cast.destinations()[0].locator());
                // Compute the randomizer as `HashToScalar(tvk || index)`.
                let randomizer = N::hash_to_scalar_psd2(&[registers.tvk()?, index])?;
                // Compute the nonce from the randomizer.
                let nonce = N::g_scalar_multiply(&randomizer);

                // Construct the record.
                let record = Record::<N, Plaintext<N>>::from_plaintext(owner, gates, entries, nonce)?;
                // Store the record.
                registers.store(self, &cast.destinations()[0], Value::Record(record))
            }
            RegisterType::ExternalRecord(_locator) => {
                bail!("Illegal operation: Cannot cast to an external record.")
            }
        }
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute_cast<A: circuit::Aleo<Network = N>>(
        &self,
        cast: &Cast<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        use circuit::{Eject, Inject, ToBits};

        // Load the operands values.
        let inputs: Vec<_> =
            cast.operands().iter().map(|operand| registers.load_circuit(self, operand)).try_collect()?;

        match cast.register_type() {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => bail!("Casting to literal is currently unsupported"),
            RegisterType::Plaintext(PlaintextType::Struct(struct_)) => {
                // Ensure the operands is not empty.
                ensure!(!inputs.is_empty(), "Casting to a struct requires at least one operand");

                // Retrieve the struct and ensure it is defined in the program.
                let struct_ = self.program().get_struct(&struct_)?;

                // Initialize the struct members.
                let mut members = IndexMap::new();
                for (member, (member_name, member_type)) in inputs.iter().zip_eq(struct_.members()) {
                    // Compute the register type.
                    let register_type = RegisterType::Plaintext(*member_type);
                    // Retrieve the plaintext value from the entry.
                    let plaintext = match member {
                        circuit::Value::Plaintext(plaintext) => {
                            // Ensure the member matches the register type.
                            self.matches_register_type(
                                &circuit::Value::Plaintext(plaintext.clone()).eject_value(),
                                &register_type,
                            )?;
                            // Output the plaintext.
                            plaintext.clone()
                        }
                        // Ensure the struct member is not a record.
                        circuit::Value::Record(..) => {
                            bail!("Casting a record into a struct member is illegal")
                        }
                    };
                    // Append the member to the struct members.
                    members.insert(circuit::Identifier::constant(*member_name), plaintext);
                }

                // Construct the struct.
                let struct_ = circuit::Plaintext::Struct(members, Default::default());
                // Store the struct.
                registers.store_circuit(self, &cast.destinations()[0], circuit::Value::Plaintext(struct_))
            }
            RegisterType::Record(record_name) => {
                // Ensure the operands length is at least 2.
                ensure!(inputs.len() >= 2, "Casting to a record requires at least two operands");

                // Retrieve the struct and ensure it is defined in the program.
                let record_type = self.program().get_record(&record_name)?;

                // Initialize the record owner.
                let owner: circuit::Owner<A, circuit::Plaintext<A>> = match &inputs[0] {
                    // Ensure the entry is an address.
                    circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Address(owner), ..)) => {
                        match record_type.owner().is_public() {
                            true => circuit::Owner::Public(owner.clone()),
                            false => circuit::Owner::Private(circuit::Plaintext::Literal(
                                circuit::Literal::Address(owner.clone()),
                                Default::default(),
                            )),
                        }
                    }
                    _ => bail!("Invalid record 'owner'"),
                };

                // Initialize the record gates.
                let gates: circuit::Balance<A, circuit::Plaintext<A>> = match &inputs[1] {
                    // Ensure the entry is a u64.
                    circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::U64(gates), ..)) => {
                        // Ensure the gates is less than or equal to 2^52.
                        A::assert(
                            !gates.to_bits_le()[52..]
                                .iter()
                                .fold(circuit::Boolean::constant(false), |acc, bit| acc | bit),
                        );
                        // Construct the record gates.
                        match record_type.gates().is_public() {
                            true => circuit::Balance::Public(gates.clone()),
                            false => circuit::Balance::Private(circuit::Plaintext::Literal(
                                circuit::Literal::U64(gates.clone()),
                                Default::default(),
                            )),
                        }
                    }
                    _ => bail!("Invalid record 'gates'"),
                };

                // Initialize the record entries.
                let mut entries = IndexMap::new();
                for (entry, (entry_name, entry_type)) in inputs.iter().skip(2).zip_eq(record_type.entries()) {
                    // Compute the register type.
                    let register_type = RegisterType::from(ValueType::from(*entry_type));
                    // Retrieve the plaintext value from the entry.
                    let plaintext = match entry {
                        circuit::Value::Plaintext(plaintext) => {
                            // Ensure the entry matches the register type.
                            self.matches_register_type(
                                &circuit::Value::Plaintext(plaintext.clone()).eject_value(),
                                &register_type,
                            )?;
                            // Output the plaintext.
                            plaintext.clone()
                        }
                        // Ensure the record entry is not a record.
                        circuit::Value::Record(..) => bail!("Casting a record into a record entry is illegal"),
                    };
                    // Construct the entry name constant circuit.
                    let entry_name = circuit::Identifier::constant(*entry_name);
                    // Append the entry to the record entries.
                    match entry_type {
                        EntryType::Constant(..) => entries.insert(entry_name, circuit::Entry::Constant(plaintext)),
                        EntryType::Public(..) => entries.insert(entry_name, circuit::Entry::Public(plaintext)),
                        EntryType::Private(..) => entries.insert(entry_name, circuit::Entry::Private(plaintext)),
                    };
                }

                // Prepare the index as a constant field element.
                let index = circuit::Field::constant(Field::from_u64(cast.destinations()[0].locator()));
                // Compute the randomizer as `HashToScalar(tvk || index)`.
                let randomizer = A::hash_to_scalar_psd2(&[registers.tvk_circuit()?, index]);
                // Compute the nonce from the randomizer.
                let nonce = A::g_scalar_multiply(&randomizer);

                // Construct the record.
                let record = circuit::Record::<A, circuit::Plaintext<A>>::from_plaintext(owner, gates, entries, nonce)?;
                // Store the record.
                registers.store_circuit(self, &cast.destinations()[0], circuit::Value::Record(record))
            }
            RegisterType::ExternalRecord(_locator) => {
                bail!("Illegal operation: Cannot cast to an external record.")
            }
        }
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn cast_output_types(&self, cast: &Cast<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of operands is correct.
        ensure!(
            input_types.len() == cast.operands().len(),
            "Instruction '{}' expects {} operands, found {} operands",
            Cast::<N>::opcode(),
            input_types.len(),
            cast.operands().len(),
        );

        // Ensure the output type is defined in the program.
        match cast.register_type() {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => bail!("Casting to literal is currently unsupported"),
            RegisterType::Plaintext(PlaintextType::Struct(struct_name)) => {
                // Retrieve the struct and ensure it is defined in the program.
                let struct_ = self.program().get_struct(&struct_name)?;
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
                let record = self.program().get_record(&record_name)?;

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

        Ok(vec![*cast.register_type()])
    }
}
