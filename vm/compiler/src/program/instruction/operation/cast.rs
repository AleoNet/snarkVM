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

use crate::{Opcode, Operand, Registers, Stack};
use console::{
    network::prelude::*,
    program::{
        Balance,
        Entry,
        EntryType,
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
};

use indexmap::IndexMap;

/// Casts the operands into the declared type.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Cast<N: Network> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
    /// The casted register type.
    register_type: RegisterType<N>,
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

    /// Returns the casted register type.
    #[inline]
    pub const fn register_type(&self) -> &RegisterType<N> {
        &self.register_type
    }
}

impl<N: Network> Cast<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Load the operands values.
        let inputs: Vec<_> = self.operands.iter().map(|operand| registers.load(stack, operand)).try_collect()?;

        match self.register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => bail!("Casting to literal is currently unsupported"),
            RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                // Ensure the operands is not empty.
                ensure!(!inputs.is_empty(), "Casting to an interface requires at least one operand");

                // Retrieve the interface and ensure it is defined in the program.
                let interface = stack.program().get_interface(&interface_name)?;

                // Initialize the interface members.
                let mut members = IndexMap::new();
                for (member, (member_name, member_type)) in inputs.iter().zip_eq(interface.members()) {
                    // Compute the register type.
                    let register_type = RegisterType::Plaintext(*member_type);
                    // Retrieve the plaintext value from the entry.
                    let plaintext = match member {
                        Value::Plaintext(plaintext) => {
                            // Ensure the member matches the register type.
                            stack.matches_register_type(&Value::Plaintext(plaintext.clone()), &register_type)?;
                            // Output the plaintext.
                            plaintext.clone()
                        }
                        // Ensure the interface member is not a record.
                        Value::Record(..) => bail!("Casting a record into an interface member is illegal"),
                    };
                    // Append the member to the interface members.
                    members.insert(*member_name, plaintext);
                }

                // Construct the interface.
                let interface = Plaintext::Interface(members, Default::default());
                // Store the interface.
                registers.store(stack, &self.destination, Value::Plaintext(interface))
            }
            RegisterType::Record(record_name) => {
                // Ensure the operands length is at least 2.
                ensure!(inputs.len() >= 2, "Casting to a record requires at least two operands");

                // Retrieve the interface and ensure it is defined in the program.
                let record_type = stack.program().get_record(&record_name)?;

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

                // Construct the record.
                let record = Record::from_plaintext(owner, gates, entries)?;
                // Store the record.
                registers.store(stack, &self.destination, Value::Record(record))
            }
            RegisterType::ExternalRecord(_locator) => {
                bail!("Illegal operation: Cannot cast to an external record.")
            }
        }
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        use circuit::{Eject, Inject, ToBits};

        // Load the operands values.
        let inputs: Vec<_> =
            self.operands.iter().map(|operand| registers.load_circuit(stack, operand)).try_collect()?;

        match self.register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => bail!("Casting to literal is currently unsupported"),
            RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                // Ensure the operands is not empty.
                ensure!(!inputs.is_empty(), "Casting to an interface requires at least one operand");

                // Retrieve the interface and ensure it is defined in the program.
                let interface = stack.program().get_interface(&interface_name)?;

                // Initialize the interface members.
                let mut members = IndexMap::new();
                for (member, (member_name, member_type)) in inputs.iter().zip_eq(interface.members()) {
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
                        // Ensure the interface member is not a record.
                        circuit::Value::Record(..) => {
                            bail!("Casting a record into an interface member is illegal")
                        }
                    };
                    // Append the member to the interface members.
                    members.insert(circuit::Identifier::constant(*member_name), plaintext);
                }

                // Construct the interface.
                let interface = circuit::Plaintext::Interface(members, Default::default());
                // Store the interface.
                registers.store_circuit(stack, &self.destination, circuit::Value::Plaintext(interface))
            }
            RegisterType::Record(record_name) => {
                // Ensure the operands length is at least 2.
                ensure!(inputs.len() >= 2, "Casting to a record requires at least two operands");

                // Retrieve the interface and ensure it is defined in the program.
                let record_type = stack.program().get_record(&record_name)?;

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

                // Construct the record.
                let record = circuit::program::Record::from_plaintext(owner, gates, entries)?;
                // Store the record.
                registers.store_circuit(stack, &self.destination, circuit::Value::Record(record))
            }
            RegisterType::ExternalRecord(_locator) => {
                bail!("Illegal operation: Cannot cast to an external record.")
            }
        }
    }

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
            RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                // Retrieve the interface and ensure it is defined in the program.
                let interface = stack.program().get_interface(&interface_name)?;
                // Ensure the input types match the interface.
                for ((_, member_type), input_type) in interface.members().iter().zip_eq(input_types) {
                    match input_type {
                        // Ensure the plaintext type matches the member type.
                        RegisterType::Plaintext(plaintext_type) => {
                            ensure!(
                                member_type == plaintext_type,
                                "Interface '{interface_name}' member type mismatch: expected '{member_type}', found '{plaintext_type}'"
                            )
                        }
                        // Ensure the input type cannot be a record (this is unsupported behavior).
                        RegisterType::Record(record_name) => bail!(
                            "Interface '{interface_name}' member type mismatch: expected '{member_type}', found record '{record_name}'"
                        ),
                        // Ensure the input type cannot be an external record (this is unsupported behavior).
                        RegisterType::ExternalRecord(locator) => bail!(
                            "Interface '{interface_name}' member type mismatch: expected '{member_type}', found external record '{locator}'"
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
        let (string, operands) = map_res(many1(parse_operand), |operands: Vec<Operand<N>>| {
            // Ensure the number of operands is within the bounds.
            match operands.len() <= N::MAX_OPERANDS {
                true => Ok(operands),
                false => Err(error("Failed to parse 'cast' opcode: too many operands")),
            }
        })(string)?;
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
        // Parse the register type from the string.
        let (string, register_type) = RegisterType::parse(string)?;

        Ok((string, Self { operands, destination, register_type }))
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
        if self.operands.len().is_zero() || self.operands.len() > N::MAX_OPERANDS {
            eprintln!("The number of operands must be nonzero and <= {}", N::MAX_OPERANDS);
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{} ", operand))?;
        write!(f, "into {} as {}", self.destination, self.register_type)
    }
}

impl<N: Network> FromBytes for Cast<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of operands.
        let num_operands = u8::read_le(&mut reader)? as usize;

        // Ensure the number of operands is within the bounds.
        if num_operands.is_zero() || num_operands > N::MAX_OPERANDS {
            return Err(error(format!("The number of operands must be nonzero and <= {}", N::MAX_OPERANDS)));
        }

        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(num_operands);
        // Read the operands.
        for _ in 0..num_operands {
            operands.push(Operand::read_le(&mut reader)?);
        }

        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;

        // Read the casted register type.
        let register_type = RegisterType::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self { operands, destination, register_type })
    }
}

impl<N: Network> ToBytes for Cast<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is within the bounds.
        if self.operands.len().is_zero() || self.operands.len() > N::MAX_OPERANDS {
            return Err(error(format!("The number of operands must be nonzero and <= {}", N::MAX_OPERANDS)));
        }

        // Write the number of operands.
        (self.operands.len() as u8).write_le(&mut writer)?;
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer)?;
        // Write the casted register type.
        self.register_type.write_le(&mut writer)
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
            Cast::<CurrentNetwork>::parse("cast r0.owner r0.gates r0.token_amount into r1 as token.record").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(cast.operands.len(), 3, "The number of operands is incorrect");
        assert_eq!(
            cast.operands[0],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("owner").unwrap()])),
            "The first operand is incorrect"
        );
        assert_eq!(
            cast.operands[1],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("gates").unwrap()])),
            "The second operand is incorrect"
        );
        assert_eq!(
            cast.operands[2],
            Operand::Register(Register::Member(0, vec![Identifier::from_str("token_amount").unwrap()])),
            "The third operand is incorrect"
        );
        assert_eq!(cast.destination, Register::Locator(1), "The destination register is incorrect");
        assert_eq!(
            cast.register_type,
            RegisterType::Record(Identifier::from_str("token").unwrap()),
            "The value type is incorrect"
        );
    }
}
