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

use crate::{
    traits::{
        RegistersCaller,
        RegistersCallerCircuit,
        RegistersLoad,
        RegistersLoadCircuit,
        RegistersStore,
        RegistersStoreCircuit,
        StackMatches,
        StackProgram,
    },
    Opcode,
    Operand,
};
use console::{
    network::prelude::*,
    program::{
        Entry,
        EntryType,
        Identifier,
        Literal,
        LiteralType,
        Owner,
        Plaintext,
        PlaintextType,
        Record,
        Register,
        RegisterType,
        Value,
        ValueType,
    },
    types::Field,
};

use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq, Hash)]
/// The type of the cast operation.
pub enum CastType<N: Network> {
    GroupXCoordinate,
    GroupYCoordinate,
    RegisterType(RegisterType<N>),
}

impl<N: Network> Parser for CastType<N> {
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the cast type from the string.
        alt((
            map(tag("group.x"), |_| Self::GroupXCoordinate),
            map(tag("group.y"), |_| Self::GroupYCoordinate),
            map(RegisterType::parse, |register_type| Self::RegisterType(register_type)),
        ))(string)
    }
}

impl<N: Network> Display for CastType<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::GroupXCoordinate => write!(f, "group.x"),
            Self::GroupYCoordinate => write!(f, "group.y"),
            Self::RegisterType(register_type) => write!(f, "{}", register_type),
        }
    }
}

impl<N: Network> Debug for CastType<N> {
    /// Prints the cast type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> FromStr for CastType<N> {
    type Err = Error;

    /// Returns a cast type from a string literal.
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> ToBytes for CastType<N> {
    /// Writes the cast type to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::GroupXCoordinate => 0u8.write_le(&mut writer),
            Self::GroupYCoordinate => 1u8.write_le(&mut writer),
            Self::RegisterType(register_type) => {
                2u8.write_le(&mut writer).and_then(|_| register_type.write_le(&mut writer))
            }
        }
    }
}

impl<N: Network> FromBytes for CastType<N> {
    /// Reads the cast type from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => Ok(Self::GroupXCoordinate),
            1 => Ok(Self::GroupYCoordinate),
            2 => Ok(Self::RegisterType(RegisterType::read_le(&mut reader)?)),
            3.. => Err(error(format!("Failed to deserialize cast type variant {variant}"))),
        }
    }
}

/// Casts the operands into the declared type.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Cast<N: Network> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
    /// The cast type.
    cast_type: CastType<N>,
}

impl<N: Network> Cast<N> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Cast
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }

    /// Returns the register type.
    #[inline]
    pub fn register_type(&self) -> &RegisterType<N> {
        match &self.cast_type {
            CastType::GroupXCoordinate | CastType::GroupYCoordinate => {
                &RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field))
            }
            CastType::RegisterType(register_type) => register_type,
        }
    }

    /// Returns the cast type.
    #[inline]
    pub const fn cast_type(&self) -> &CastType<N> {
        &self.cast_type
    }
}

impl<N: Network> Cast<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersCaller<N> + RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> = self.operands.iter().map(|operand| registers.load(stack, operand)).try_collect()?;

        match self.cast_type {
            CastType::GroupXCoordinate => {
                ensure!(inputs.len() == 1, "Casting to a group x-coordinate requires exactly 1 operand");
                let field = match &inputs[0] {
                    Value::Plaintext(Plaintext::Literal(Literal::Group(group), ..)) => group.to_x_coordinate(),
                    _ => bail!("Casting to a group x-coordinate requires a group element"),
                };
                registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(Literal::Field(field))))
            }
            CastType::GroupYCoordinate => {
                ensure!(inputs.len() == 1, "Casting to a group y-coordinate requires exactly 1 operand");
                let field = match &inputs[0] {
                    Value::Plaintext(Plaintext::Literal(Literal::Group(group), ..)) => group.to_y_coordinate(),
                    _ => bail!("Casting to a group y-coordinate requires a group element"),
                };
                registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(Literal::Field(field))))
            }
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Literal(literal_type))) => {
                ensure!(inputs.len() == 1, "Casting to a literal requires exactly 1 operand");
                let value = match &inputs[0] {
                    Value::Plaintext(Plaintext::Literal(literal, ..)) => literal.downcast(literal_type)?,
                    _ => bail!("Casting to a literal requires a literal"),
                };
                registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(value)))
            }
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Struct(struct_name))) => {
                self.cast_to_struct(stack, registers, struct_name, inputs)
            }
            CastType::RegisterType(RegisterType::Record(record_name)) => {
                // Ensure the operands length is at least the minimum.
                if inputs.len() < N::MIN_RECORD_ENTRIES {
                    bail!("Casting to a record requires at least {} operand", N::MIN_RECORD_ENTRIES)
                }

                // Retrieve the struct and ensure it is defined in the program.
                let record_type = stack.program().get_record(&record_name)?;

                // Ensure that the number of operands is equal to the number of record entries, including the `owner`.
                if inputs.len() != record_type.entries().len() + 1 {
                    bail!(
                        "Casting to the record {} requires {} operands, but {} were provided",
                        record_type.name(),
                        record_type.entries().len() + 1,
                        inputs.len()
                    )
                }

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

                // Initialize the record entries.
                let mut entries = IndexMap::new();
                for (entry, (entry_name, entry_type)) in
                    inputs.iter().skip(N::MIN_RECORD_ENTRIES).zip_eq(record_type.entries())
                {
                    // Compute the register type.
                    let register_type = RegisterType::from(ValueType::from(*entry_type));
                    // Retrieve the plaintext value from the entry.
                    let plaintext = match entry {
                        Value::Plaintext(plaintext) => {
                            // Ensure the entry matches the register type.
                            stack.matches_register_type(&Value::Plaintext(plaintext.clone()), &register_type)?;
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
                let index = Field::from_u64(self.destination.locator());
                // Compute the randomizer as `HashToScalar(tvk || index)`.
                let randomizer = N::hash_to_scalar_psd2(&[registers.tvk()?, index])?;
                // Compute the nonce from the randomizer.
                let nonce = N::g_scalar_multiply(&randomizer);

                // Construct the record.
                let record = Record::<N, Plaintext<N>>::from_plaintext(owner, entries, nonce)?;
                // Store the record.
                registers.store(stack, &self.destination, Value::Record(record))
            }
            CastType::RegisterType(RegisterType::ExternalRecord(_locator)) => {
                bail!("Illegal operation: Cannot cast to an external record.")
            }
        }
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersCallerCircuit<N, A> + RegistersLoadCircuit<N, A> + RegistersStoreCircuit<N, A>),
    ) -> Result<()> {
        use circuit::{Eject, Inject};

        // Load the operands values.
        let inputs: Vec<_> =
            self.operands.iter().map(|operand| registers.load_circuit(stack, operand)).try_collect()?;

        match self.cast_type {
            CastType::GroupXCoordinate => {
                ensure!(inputs.len() == 1, "Casting to a group x-coordinate requires exactly 1 operand");
                let field = match &inputs[0] {
                    circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Group(group), ..)) => {
                        group.to_x_coordinate()
                    }
                    _ => bail!("Casting to a group x-coordinate requires a group element"),
                };
                registers.store_circuit(
                    stack,
                    &self.destination,
                    circuit::Value::Plaintext(circuit::Plaintext::from(circuit::Literal::Field(field))),
                )
            }
            CastType::GroupYCoordinate => {
                ensure!(inputs.len() == 1, "Casting to a group y-coordinate requires exactly 1 operand");
                let field = match &inputs[0] {
                    circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Group(group), ..)) => {
                        group.to_y_coordinate()
                    }
                    _ => bail!("Casting to a group y-coordinate requires a group element"),
                };
                registers.store_circuit(
                    stack,
                    &self.destination,
                    circuit::Value::Plaintext(circuit::Plaintext::from(circuit::Literal::Field(field))),
                )
            }
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Literal(literal_type))) => {
                ensure!(inputs.len() == 1, "Casting to a literal requires exactly 1 operand");
                let value = match &inputs[0] {
                    circuit::Value::Plaintext(circuit::Plaintext::Literal(literal, ..)) => {
                        literal.downcast(literal_type)?
                    }
                    _ => bail!("Casting to a literal requires a literal"),
                };
                registers.store_circuit(
                    stack,
                    &self.destination,
                    circuit::Value::Plaintext(circuit::Plaintext::from(value)),
                )
            }
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Struct(struct_))) => {
                // Ensure the operands length is at least the minimum.
                if inputs.len() < N::MIN_STRUCT_ENTRIES {
                    bail!("Casting to a struct requires at least {} operand", N::MIN_STRUCT_ENTRIES)
                }

                // Retrieve the struct and ensure it is defined in the program.
                let struct_ = stack.program().get_struct(&struct_)?;

                // Ensure that the number of operands is equal to the number of struct members.
                if inputs.len() != struct_.members().len() {
                    bail!(
                        "Casting to the struct {} requires {} operands, but {} were provided",
                        struct_.name(),
                        struct_.members().len(),
                        inputs.len()
                    )
                }

                // Initialize the struct members.
                let mut members = IndexMap::new();
                for (member, (member_name, member_type)) in inputs.iter().zip_eq(struct_.members()) {
                    // Compute the register type.
                    let register_type = RegisterType::Plaintext(*member_type);
                    // Retrieve the plaintext value from the entry.
                    let plaintext = match member {
                        circuit::Value::Plaintext(plaintext) => {
                            // Ensure the member matches the register type.
                            stack.matches_register_type(
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
                registers.store_circuit(stack, &self.destination, circuit::Value::Plaintext(struct_))
            }
            CastType::RegisterType(RegisterType::Record(record_name)) => {
                // Ensure the operands length is at least the minimum.
                if inputs.len() < N::MIN_RECORD_ENTRIES {
                    bail!("Casting to a record requires at least {} operand", N::MIN_RECORD_ENTRIES)
                }

                // Retrieve the struct and ensure it is defined in the program.
                let record_type = stack.program().get_record(&record_name)?;

                // Ensure that the number of operands is equal to the number of record entries, including the `owner`.
                if inputs.len() != record_type.entries().len() + 1 {
                    bail!(
                        "Casting to the record {} requires {} operands, but {} were provided",
                        record_type.name(),
                        record_type.entries().len() + 1,
                        inputs.len()
                    )
                }

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

                // Initialize the record entries.
                let mut entries = IndexMap::new();
                for (entry, (entry_name, entry_type)) in
                    inputs.iter().skip(N::MIN_RECORD_ENTRIES).zip_eq(record_type.entries())
                {
                    // Compute the register type.
                    let register_type = RegisterType::from(ValueType::from(*entry_type));
                    // Retrieve the plaintext value from the entry.
                    let plaintext = match entry {
                        circuit::Value::Plaintext(plaintext) => {
                            // Ensure the entry matches the register type.
                            stack.matches_register_type(
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
                let index = circuit::Field::constant(Field::from_u64(self.destination.locator()));
                // Compute the randomizer as `HashToScalar(tvk || index)`.
                let randomizer = A::hash_to_scalar_psd2(&[registers.tvk_circuit()?, index]);
                // Compute the nonce from the randomizer.
                let nonce = A::g_scalar_multiply(&randomizer);

                // Construct the record.
                let record = circuit::Record::<A, circuit::Plaintext<A>>::from_plaintext(owner, entries, nonce)?;
                // Store the record.
                registers.store_circuit(stack, &self.destination, circuit::Value::Record(record))
            }
            CastType::RegisterType(RegisterType::ExternalRecord(_locator)) => {
                bail!("Illegal operation: Cannot cast to an external record.")
            }
        }
    }

    /// Finalizes the instruction.
    #[inline]
    pub fn finalize(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> = self.operands.iter().map(|operand| registers.load(stack, operand)).try_collect()?;

        match self.cast_type {
            CastType::GroupXCoordinate => {
                ensure!(inputs.len() == 1, "Casting to a group x-coordinate requires exactly 1 operand");
                let field = match &inputs[0] {
                    Value::Plaintext(Plaintext::Literal(Literal::Group(group), ..)) => group.to_x_coordinate(),
                    _ => bail!("Casting to a group x-coordinate requires a group element"),
                };
                registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(Literal::Field(field))))
            }
            CastType::GroupYCoordinate => {
                ensure!(inputs.len() == 1, "Casting to a group y-coordinate requires exactly 1 operand");
                let field = match &inputs[0] {
                    Value::Plaintext(Plaintext::Literal(Literal::Group(group), ..)) => group.to_y_coordinate(),
                    _ => bail!("Casting to a group y-coordinate requires a group element"),
                };
                registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(Literal::Field(field))))
            }
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Literal(literal_type))) => {
                ensure!(inputs.len() == 1, "Casting to a literal requires exactly 1 operand");
                let value = match &inputs[0] {
                    Value::Plaintext(Plaintext::Literal(literal, ..)) => literal.downcast(literal_type)?,
                    _ => bail!("Casting to a literal requires a literal"),
                };
                registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(value)))
            }
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Struct(struct_name))) => {
                self.cast_to_struct(stack, registers, struct_name, inputs)
            }
            CastType::RegisterType(RegisterType::Record(_record_name)) => {
                bail!("Illegal operation: Cannot cast to a record in a finalize block.")
            }
            CastType::RegisterType(RegisterType::ExternalRecord(_locator)) => {
                bail!("Illegal operation: Cannot cast to an external record.")
            }
        }
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(
        &self,
        stack: &impl StackProgram<N>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of operands is correct.
        ensure!(
            input_types.len() == self.operands.len(),
            "Instruction '{}' expects {} operands, found {} operands",
            Self::opcode(),
            input_types.len(),
            self.operands.len(),
        );

        // Ensure the output type is defined in the program.
        match self.cast_type {
            CastType::GroupXCoordinate | CastType::GroupYCoordinate => {
                ensure!(input_types.len() == 1, "Casting to a group coordinate requires exactly 1 operand");
                ensure!(
                    matches!(input_types[0], RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Group))),
                    "Type mismatch: expected 'group', found '{}'",
                    input_types[0]
                );
            }
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Literal(..))) => {
                ensure!(input_types.len() == 1, "Casting to a literal requires exactly 1 operand");
            }
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Struct(struct_name))) => {
                // Retrieve the struct and ensure it is defined in the program.
                let struct_ = stack.program().get_struct(&struct_name)?;
                // Ensure that the input types length is at least the minimum.
                ensure!(
                    input_types.len() >= N::MIN_STRUCT_ENTRIES,
                    "Casting to a struct requires at least {} operand",
                    N::MIN_STRUCT_ENTRIES
                );
                // Ensure that the number of input types is equal to the number of struct members.
                ensure!(
                    input_types.len() == struct_.members().len(),
                    "Casting to the struct {} requires {} operands, but {} were provided",
                    struct_.name(),
                    struct_.members().len(),
                    input_types.len()
                );
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
            CastType::RegisterType(RegisterType::Record(record_name)) => {
                // Retrieve the record type and ensure is defined in the program.
                let record = stack.program().get_record(&record_name)?;

                // Ensure the input types length is at least the minimum.
                ensure!(
                    input_types.len() >= N::MIN_RECORD_ENTRIES,
                    "Casting to a record requires at least {} operands",
                    N::MIN_RECORD_ENTRIES
                );
                // Ensure that the number of input types is equal to the number of record entries, including the `owner`.
                ensure!(
                    input_types.len() == record.entries().len() + 1,
                    "Casting to the record {} requires {} operands, but {} were provided",
                    record.name(),
                    record.entries().len() + 1,
                    input_types.len()
                );
                // Ensure the first input type is an address.
                ensure!(
                    input_types[0] == RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address)),
                    "Casting to a record requires the first operand to be an address"
                );

                // Ensure the input types match the record.
                for (input_type, (_, entry_type)) in
                    input_types.iter().skip(N::MIN_RECORD_ENTRIES).zip_eq(record.entries())
                {
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
            CastType::RegisterType(RegisterType::ExternalRecord(_locator)) => {
                bail!("Illegal operation: Cannot cast to an external record.")
            }
        }

        Ok(vec![match self.cast_type {
            CastType::GroupXCoordinate | CastType::GroupYCoordinate => {
                RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field))
            }
            CastType::RegisterType(register_type) => register_type,
        }])
    }
}

impl<N: Network> Cast<N> {
    /// A helper method to handle casting to a struct.
    fn cast_to_struct(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut impl RegistersStore<N>,
        struct_name: Identifier<N>,
        inputs: Vec<Value<N>>,
    ) -> Result<()> {
        // Ensure the operands length is at least the minimum.
        if inputs.len() < N::MIN_STRUCT_ENTRIES {
            bail!("Casting to a struct requires at least {} operand", N::MIN_STRUCT_ENTRIES)
        }

        // Retrieve the struct and ensure it is defined in the program.
        let struct_ = stack.program().get_struct(&struct_name)?;

        // Ensure that the number of operands is equal to the number of struct members.
        if inputs.len() != struct_.members().len() {
            bail!(
                "Casting to the struct {} requires {} operands, but {} were provided",
                struct_.name(),
                struct_.members().len(),
                inputs.len()
            )
        }

        // Initialize the struct members.
        let mut members = IndexMap::new();
        for (member, (member_name, member_type)) in inputs.iter().zip_eq(struct_.members()) {
            // Retrieve the plaintext value from the entry.
            let plaintext = match member {
                Value::Plaintext(plaintext) => {
                    // Ensure the plaintext matches the member type.
                    stack.matches_plaintext(plaintext, member_type)?;
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
        registers.store(stack, &self.destination, Value::Plaintext(struct_))
    }
}

impl<N: Network> Parser for Cast<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        /// Parses an operand from the string.
        fn parse_operand<N: Network>(string: &str) -> ParserResult<Operand<N>> {
            // Parse the whitespace from the string.
            let (string, _) = Sanitizer::parse_whitespaces(string)?;
            // Parse the operand from the string.
            Operand::parse(string)
        }

        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the operands from the string.
        let (string, operands) = many1(parse_operand)(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "as" from the string.
        let (string, _) = tag("as")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the cast type from the string.
        let (string, cast_type) = CastType::parse(string)?;
        // Check that the number of operands does not exceed the maximum number of data entries.
        let max_operands = match cast_type {
            CastType::GroupXCoordinate
            | CastType::GroupYCoordinate
            | CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Literal(_))) => 1,
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Struct(_))) => N::MAX_STRUCT_ENTRIES,
            CastType::RegisterType(RegisterType::Record(_))
            | CastType::RegisterType(RegisterType::ExternalRecord(_)) => N::MAX_RECORD_ENTRIES,
        };
        match !operands.is_empty() && (operands.len() <= max_operands) {
            true => Ok((string, Self { operands, destination, cast_type })),
            false => {
                map_res(fail, |_: ParserResult<Self>| Err(error("Failed to parse 'cast' opcode: too many operands")))(
                    string,
                )
            }
        }
    }
}

impl<N: Network> FromStr for Cast<N> {
    type Err = Error;

    /// Parses a string into an operation.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for Cast<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Cast<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is within the bounds.
        let max_operands = match self.cast_type {
            CastType::GroupYCoordinate
            | CastType::GroupXCoordinate
            | CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Literal(_))) => 1,
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Struct(_))) => N::MAX_STRUCT_ENTRIES,
            CastType::RegisterType(RegisterType::Record(_))
            | CastType::RegisterType(RegisterType::ExternalRecord(_)) => N::MAX_RECORD_ENTRIES,
        };
        if self.operands.is_empty() || self.operands.len() > max_operands {
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{operand} "))?;
        write!(f, "into {} as {}", self.destination, self.cast_type)
    }
}

impl<N: Network> FromBytes for Cast<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of operands.
        let num_operands = u8::read_le(&mut reader)? as usize;

        // Ensure that the number of operands does not exceed the upper bound.
        // Note: Although a similar check is performed later, this check is performed to ensure that an exceedingly large number of operands is not allocated.
        // Note: This check is purely a sanity check, as it is not type-aware.
        if num_operands.is_zero() || num_operands > N::MAX_RECORD_ENTRIES {
            return Err(error(format!("The number of operands must be nonzero and <= {}", N::MAX_RECORD_ENTRIES)));
        }

        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(num_operands);
        // Read the operands.
        for _ in 0..num_operands {
            operands.push(Operand::read_le(&mut reader)?);
        }

        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;

        // Read the cast type.
        let cast_type = CastType::read_le(&mut reader)?;

        // Ensure the number of operands is within the bounds for the cast type.
        let max_operands = match cast_type {
            CastType::GroupYCoordinate
            | CastType::GroupXCoordinate
            | CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Literal(_))) => 1,
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Struct(_))) => N::MAX_STRUCT_ENTRIES,
            CastType::RegisterType(RegisterType::Record(_))
            | CastType::RegisterType(RegisterType::ExternalRecord(_)) => N::MAX_RECORD_ENTRIES,
        };
        if num_operands.is_zero() || num_operands > max_operands {
            return Err(error(format!("The number of operands must be nonzero and <= {max_operands}")));
        }

        // Return the operation.
        Ok(Self { operands, destination, cast_type })
    }
}

impl<N: Network> ToBytes for Cast<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is within the bounds.
        let max_operands = match self.cast_type {
            CastType::GroupYCoordinate
            | CastType::GroupXCoordinate
            | CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Literal(_))) => 1,
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Struct(_))) => N::MAX_STRUCT_ENTRIES,
            CastType::RegisterType(RegisterType::Record(_))
            | CastType::RegisterType(RegisterType::ExternalRecord(_)) => N::MAX_RECORD_ENTRIES,
        };
        if self.operands.is_empty() || self.operands.len() > max_operands {
            return Err(error(format!("The number of operands must be nonzero and <= {max_operands}")));
        }

        // Write the number of operands.
        u8::try_from(self.operands.len()).map_err(|e| error(e.to_string()))?.write_le(&mut writer)?;
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer)?;
        // Write the cast type.
        self.cast_type.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{network::Testnet3, program::Identifier};

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, cast) =
            Cast::<CurrentNetwork>::parse("cast r0.owner r0.token_amount into r1 as token.record").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(cast.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(
            cast.operands[0],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("owner").unwrap()])),
            "The first operand is incorrect"
        );
        assert_eq!(
            cast.operands[1],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("token_amount").unwrap()])),
            "The second operand is incorrect"
        );
        assert_eq!(cast.destination, Register::Locator(1), "The destination register is incorrect");
        assert_eq!(
            cast.cast_type,
            CastType::RegisterType(RegisterType::Record(Identifier::from_str("token").unwrap())),
            "The value type is incorrect"
        );
    }

    #[test]
    fn test_parse_cast_into_plaintext_max_operands() {
        let mut string = "cast ".to_string();
        let mut operands = Vec::with_capacity(CurrentNetwork::MAX_STRUCT_ENTRIES);
        for i in 0..CurrentNetwork::MAX_STRUCT_ENTRIES {
            string.push_str(&format!("r{i} "));
            operands.push(Operand::Register(Register::Locator(i as u64)));
        }
        string.push_str(&format!("into r{} as foo", CurrentNetwork::MAX_STRUCT_ENTRIES));
        let (string, cast) = Cast::<CurrentNetwork>::parse(&string).unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(cast.operands.len(), CurrentNetwork::MAX_STRUCT_ENTRIES, "The number of operands is incorrect");
        assert_eq!(cast.operands, operands, "The operands are incorrect");
        assert_eq!(
            cast.destination,
            Register::Locator(CurrentNetwork::MAX_STRUCT_ENTRIES as u64),
            "The destination register is incorrect"
        );
        assert_eq!(
            cast.cast_type,
            CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Struct(
                Identifier::from_str("foo").unwrap()
            ))),
            "The value type is incorrect"
        );
    }

    #[test]
    fn test_parse_cast_into_record_max_operands() {
        let mut string = "cast ".to_string();
        let mut operands = Vec::with_capacity(CurrentNetwork::MAX_RECORD_ENTRIES);
        for i in 0..CurrentNetwork::MAX_RECORD_ENTRIES {
            string.push_str(&format!("r{i} "));
            operands.push(Operand::Register(Register::Locator(i as u64)));
        }
        string.push_str(&format!("into r{} as token.record", CurrentNetwork::MAX_RECORD_ENTRIES));
        let (string, cast) = Cast::<CurrentNetwork>::parse(&string).unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(cast.operands.len(), CurrentNetwork::MAX_RECORD_ENTRIES, "The number of operands is incorrect");
        assert_eq!(cast.operands, operands, "The operands are incorrect");
        assert_eq!(
            cast.destination,
            Register::Locator((CurrentNetwork::MAX_RECORD_ENTRIES) as u64),
            "The destination register is incorrect"
        );
        assert_eq!(
            cast.cast_type,
            CastType::RegisterType(RegisterType::Record(Identifier::from_str("token").unwrap())),
            "The value type is incorrect"
        );
    }

    #[test]
    fn test_parse_cast_into_record_too_many_operands() {
        let mut string = "cast ".to_string();
        for i in 0..=CurrentNetwork::MAX_RECORD_ENTRIES {
            string.push_str(&format!("r{i} "));
        }
        string.push_str(&format!("into r{} as token.record", CurrentNetwork::MAX_RECORD_ENTRIES + 1));
        assert!(Cast::<CurrentNetwork>::parse(&string).is_err(), "Parser did not error");
    }

    #[test]
    fn test_parse_cast_into_plaintext_too_many_operands() {
        let mut string = "cast ".to_string();
        for i in 0..=CurrentNetwork::MAX_STRUCT_ENTRIES {
            string.push_str(&format!("r{i} "));
        }
        string.push_str(&format!("into r{} as foo", CurrentNetwork::MAX_STRUCT_ENTRIES + 1));
        assert!(Cast::<CurrentNetwork>::parse(&string).is_err(), "Parser did not error");
    }
}
