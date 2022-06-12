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

mod registers;
pub(crate) use registers::*;

mod stack;
pub(crate) use stack::*;

use crate::{
    function::Operand,
    Function,
    Identifier,
    Interface,
    Plaintext,
    PlaintextType,
    RecordType,
    Register,
    Value,
    ValueType,
};
use snarkvm_console_network::prelude::*;

use indexmap::IndexMap;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum ProgramDefinition {
    /// A program interface.
    Interface,
    /// A program record.
    Record,
    /// A program function.
    Function,
}

#[derive(Clone, PartialEq, Eq)]
pub struct Program<N: Network> {
    /// A map of identifiers to their program declaration.
    identifiers: IndexMap<Identifier<N>, ProgramDefinition>,
    /// A map of the declared interfaces for the program.
    interfaces: IndexMap<Identifier<N>, Interface<N>>,
    /// A map of the declared record types for the program.
    records: IndexMap<Identifier<N>, RecordType<N>>,
    /// A map of the declared functions for the program.
    functions: IndexMap<Identifier<N>, Function<N>>,
    /// A map of the declared register types for each function.
    function_registers: IndexMap<Identifier<N>, RegisterTypes<N>>,
}

impl<N: Network> Program<N> {
    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate(
        &self,
        function_name: &Identifier<N>,
        inputs: &[Plaintext<N>],
    ) -> Result<Vec<Value<N, Plaintext<N>>>> {
        // Retrieve the function from the program.
        let function = self.get_function(function_name)?;

        // Ensure the number of inputs matches the number of input statements.
        ensure!(
            function.inputs().len() == inputs.len(),
            "Expected {} inputs, found {}",
            function.inputs().len(),
            inputs.len()
        );

        // Retrieve the registers for the function.
        let register_types = self
            .function_registers
            .get(function_name)
            .ok_or_else(|| anyhow!("Function {function_name} is missing its function registers"))?;

        // Initialize the stack.
        let mut stack = Stack::new(self.clone(), register_types.clone(), inputs)?;

        // Evaluate the function.
        function.evaluate(&mut stack)?;

        // Initialize a vector to store the outputs.
        let mut outputs = Vec::with_capacity(function.outputs().len());

        // Load the outputs.
        // for output in self.outputs.iter() {
        //     // Load the value from the output register.
        //     let register = output.register();
        //     let value = self.registers.load(register);
        //
        //     // TODO (howardwu): When handling the TODO below, relax this to exclude checking the mode.
        //     // Ensure the output plaintext type matches the annotation.
        //     if &value.annotation() != output.annotation() {
        //         P::halt(format!("Output \'{register}\' has an incorrect annotation of {}", value.annotation()))
        //     }
        //
        //     // TODO (howardwu): When handling the TODO below, relax this to exclude checking the mode.
        //     // If the output annotation is a definition, ensure the output value matches the definition.
        //     if let Annotation::Definition(definition_name) = output.annotation() {
        //         // Retrieve the definition from the program.
        //         match P::get_definition(definition_name) {
        //             // Ensure the value matches its expected definition.
        //             Some(definition) => {
        //                 if !definition.matches(&value) {
        //                     P::halt(format!("Output \'{register}\' does not match \'{definition_name}\'"))
        //                 }
        //             }
        //             None => P::halt("Output \'{register}\' references a non-existent definition"),
        //         }
        //     }
        //
        //     // TODO (howardwu): Add encryption against the caller's address for all private literals,
        //     //  and inject the ciphertext as Mode::Public, along with a constraint enforcing equality.
        //     //  For constant outputs, add an assert_eq on the register value - if it's constant,
        //     //  the constraint will automatically be discarded, and if it's not, the constraint will
        //     //  ensure the output register's value matches the newly-assigned hardcoded constant.
        //     // // If the value contains any public literals, assign a new public variable for the public literal,
        //     // // and add a constraint to enforce equality of the value.
        //     // match &value {
        //     //     Value::Literal(literal) => {
        //     //         if literal.is_public() {
        //     //             let public_literal = Literal::new(Mode::Public, literal.eject_value());
        //     //             P::Environment::assert_eq(literal, public_literal);
        //     //         }
        //     //     }
        //     //     Value::Definition(_, members) => {
        //     //         for member in members.iter() {
        //     //             if member.is_public() {
        //     //                 let public_literal = Literal::new(Mode::Public, member.eject_value());
        //     //                 P::Environment::assert_eq(member, public_literal);
        //     //             }
        //     //         }
        //     //     }
        //     // }
        //
        //     // Insert the value into the outputs.
        //     outputs.push(value);
        // }

        Ok(outputs)
    }
}

impl<N: Network> Program<N> {
    /// Initializes an empty program.
    #[inline]
    pub fn new() -> Self {
        Program {
            identifiers: IndexMap::new(),
            interfaces: IndexMap::new(),
            records: IndexMap::new(),
            functions: IndexMap::new(),
            function_registers: IndexMap::new(),
        }
    }

    /// Adds a new interface to the program.
    ///
    /// # Errors
    /// This method will halt if the interface was previously added.
    /// This method will halt if the interface name is already in use in the program.
    /// This method will halt if any interfaces in the interface's members are not already defined.
    #[inline]
    fn add_interface(&mut self, interface: Interface<N>) -> Result<()> {
        // Retrieve the interface name.
        let interface_name = interface.name().clone();

        // Ensure the interface name is new.
        ensure!(self.is_unique_name(&interface_name), "'{}' is already in use.", interface_name);
        // Ensure the interface name is not a reserved keyword.
        ensure!(!self.is_reserved_name(&interface_name), "'{}' is a reserved keyword.", interface_name);

        // Ensure all interface members are well-formed.
        // Note: This design ensures cyclic references are not possible.
        for (identifier, plaintext_type) in interface.members() {
            // Ensure the member name is not a reserved keyword.
            ensure!(!self.is_reserved_name(identifier), "'{identifier}' is a reserved keyword.");
            // Ensure the member type is already defined in the program.
            match plaintext_type {
                PlaintextType::Literal(..) => continue,
                PlaintextType::Interface(member_identifier) => {
                    // Ensure the member interface name exists in the program.
                    if !self.interfaces.contains_key(member_identifier) {
                        bail!("'{member_identifier}' in interface '{}' is not defined.", interface_name)
                    }
                }
            }
        }

        // Add the interface name to the identifiers.
        if self.identifiers.insert(interface_name.clone(), ProgramDefinition::Interface).is_some() {
            bail!("'{}' already exists in the program.", interface_name)
        }
        // Add the interface to the program.
        if self.interfaces.insert(interface_name.clone(), interface).is_some() {
            bail!("'{}' already exists in the program.", interface_name)
        }
        Ok(())
    }

    /// Adds a new record to the program.
    ///
    /// # Errors
    /// This method will halt if the record was previously added.
    /// This method will halt if the record name is already in use in the program.
    /// This method will halt if any records in the record's members are not already defined.
    #[inline]
    fn add_record(&mut self, record: RecordType<N>) -> Result<()> {
        // Retrieve the record name.
        let record_name = record.name().clone();

        // Ensure the record name is new.
        ensure!(self.is_unique_name(&record_name), "'{}' is already in use.", record_name);
        // Ensure the record name is not a reserved keyword.
        ensure!(!self.is_reserved_name(&record_name), "'{}' is a reserved keyword.", record_name);

        // Ensure all record entries are well-formed.
        // Note: This design ensures cyclic references are not possible.
        for (identifier, value_type) in record.entries() {
            // Ensure the member name is not a reserved keyword.
            ensure!(!self.is_reserved_name(identifier), "'{identifier}' is a reserved keyword.");
            // Ensure the member type is already defined in the program.
            match value_type.to_plaintext_type() {
                PlaintextType::Literal(..) => continue,
                PlaintextType::Interface(identifier) => {
                    if !self.interfaces.contains_key(&identifier) {
                        bail!("'{identifier}' in record '{}' is not defined.", record_name)
                    }
                }
            }
        }

        // Add the record name to the identifiers.
        if self.identifiers.insert(record_name.clone(), ProgramDefinition::Record).is_some() {
            bail!("'{}' already exists in the program.", record_name)
        }
        // Add the record to the program.
        if self.records.insert(record_name.clone(), record).is_some() {
            bail!("'{}' already exists in the program.", record_name)
        }
        Ok(())
    }

    /// Adds a new function to the program.
    ///
    /// # Errors
    /// This method will halt if the function was previously added.
    /// This method will halt if the function name is already in use in the program.
    /// This method will halt if any registers are assigned more than once.
    /// This method will halt if the registers are not incrementing monotonically.
    /// This method will halt if an input type references a non-existent definition.
    /// This method will halt if an operand register does not already exist in memory.
    /// This method will halt if a destination register already exists in memory.
    /// This method will halt if an output register does not already exist.
    /// This method will halt if an output type references a non-existent definition.
    #[inline]
    fn add_function(&mut self, function: Function<N>) -> Result<()> {
        // Retrieve the function name.
        let function_name = function.name().clone();

        // Ensure the function name is new.
        ensure!(self.is_unique_name(&function_name), "'{}' is already in use.", function_name);
        // Ensure the function name is not a reserved keyword.
        ensure!(!self.is_reserved_name(&function_name), "'{}' is a reserved keyword.", function_name);

        // Initialize a map of registers to their types.
        let mut registers = RegisterTypes::new();

        // Step 1. Check the function inputs are well-formed.
        for input in function.inputs() {
            // Retrieve the plaintext type from the input type.
            let plaintext_type = match input.value_type() {
                ValueType::Constant(plaintext_type) => {
                    // TODO (howardwu): If the plaintext type is a record, ensure it cannot be a constant.
                    plaintext_type
                }
                ValueType::Public(plaintext_type) => plaintext_type,
                ValueType::Private(plaintext_type) => plaintext_type,
            };

            // Ensure the plaintext type is defined in the program.
            match plaintext_type {
                PlaintextType::Literal(..) => (),
                PlaintextType::Interface(interface_name) => {
                    // Ensure the interface name exists in the program.
                    if !self.interfaces.contains_key(interface_name) {
                        bail!("'{interface_name}' in function '{function_name}' is not defined.")
                    }
                }
            }

            // Insert the input register.
            registers.insert(input.register().clone(), RegisterType::Input(*input.value_type()))?;
        }

        // Step 2. Check the function instructions are well-formed.
        for instruction in function.instructions() {
            // Initialize a vector to store the plaintext types of the operands.
            let mut operand_types = Vec::with_capacity(instruction.operands().len());
            // Iterate over the operands, and retrieve the plaintext type of each operand.
            for operand in instruction.operands() {
                // Retrieve and append the plaintext type.
                operand_types.push(match operand {
                    Operand::Literal(literal) => PlaintextType::from(literal.to_type()),
                    Operand::Register(register) => registers.get_type(&self, &register)?,
                });
            }

            // Compute the destination register type.
            let destination_type = RegisterType::Destination(instruction.output_type(&operand_types)?);

            // Retrieve the destination register.
            let destination = instruction.destination();
            match destination {
                // Insert the destination register.
                Register::Locator(..) => registers.insert(destination.clone(), destination_type)?,
                // Ensure the destination register is a locator (and does not reference a member).
                Register::Member(..) => bail!("Destination register '{destination}' must be a locator."),
            }
        }

        // Step 3. Check the function outputs are well-formed.
        for output in function.outputs() {
            // Retrieve the output register.
            let register = output.register();
            // Inform the user the output register is an input register, to ensure this is intended behavior.
            if registers.is_input(register) {
                eprintln!("Output {register} is an input register, ensure this is intended behavior");
            }

            // Retrieve the register type (as a plaintext type).
            // Note: This serves as the expected output type, which we will compare against.
            let register_type = registers.get_type(&self, &register)?;

            // Retrieve the plaintext type from the output type.
            let plaintext_type = match output.value_type() {
                ValueType::Constant(plaintext_type) => {
                    // TODO (howardwu): If the plaintext type is a record, ensure it cannot be a constant.
                    plaintext_type
                }
                ValueType::Public(plaintext_type) => plaintext_type,
                ValueType::Private(plaintext_type) => plaintext_type,
            };

            // Ensure the plaintext type is defined in the program.
            match plaintext_type {
                PlaintextType::Literal(..) => (),
                PlaintextType::Interface(interface_name) => {
                    // Ensure the interface name exists in the program.
                    if !self.interfaces.contains_key(interface_name) {
                        bail!("'{interface_name}' in function '{function_name}' is not defined.")
                    }
                }
            }

            // Ensure the register type and the output type match.
            ensure!(register_type == *plaintext_type, "Output '{register}' has the wrong type.");
        }

        // Add the function name to the identifiers.
        if self.identifiers.insert(function_name.clone(), ProgramDefinition::Function).is_some() {
            bail!("'{}' already exists in the program.", function_name)
        }
        // Add the function to the program.
        if self.functions.insert(function_name.clone(), function).is_some() {
            bail!("'{}' already exists in the program.", function_name)
        }
        // Add the function registers to the program.
        if self.function_registers.insert(function_name.clone(), registers).is_some() {
            bail!("'{}' already exists in the program.", function_name)
        }
        Ok(())
    }

    /// Returns `true` if the program contains a interface with the given name.
    pub fn contains_interface(&self, name: &Identifier<N>) -> bool {
        self.interfaces.contains_key(name)
    }

    /// Returns `true` if the program contains a record with the given name.
    pub fn contains_record(&self, name: &Identifier<N>) -> bool {
        self.records.contains_key(name)
    }

    /// Returns `true` if the program contains a function with the given name.
    pub fn contains_function(&self, name: &Identifier<N>) -> bool {
        self.functions.contains_key(name)
    }

    /// Returns the interface with the given name.
    pub fn get_interface(&self, name: &Identifier<N>) -> Result<Interface<N>> {
        self.interfaces.get(name).cloned().ok_or_else(|| anyhow!("Interface '{name}' is not defined."))
    }

    /// Returns the record with the given name.
    pub fn get_record(&self, name: &Identifier<N>) -> Result<RecordType<N>> {
        self.records.get(name).cloned().ok_or_else(|| anyhow!("Record '{name}' is not defined."))
    }

    /// Returns the function with the given name.
    pub fn get_function(&self, name: &Identifier<N>) -> Result<Function<N>> {
        self.functions.get(name).cloned().ok_or_else(|| anyhow!("Function '{name}' is not defined."))
    }
}

impl<N: Network> Program<N> {
    /// Returns `true` if the given name does not already exist in the program.
    pub(crate) fn is_unique_name(&self, name: &Identifier<N>) -> bool {
        !self.identifiers.contains_key(name)
    }

    /// Returns `true` if the given name uses a reserved keyword.
    pub(crate) fn is_reserved_name(&self, name: &Identifier<N>) -> bool {
        #[rustfmt::skip]
        const KEYWORDS: &[&str] = &[
            // Mode
            "const",
            "constant",
            "public",
            "private",
            // Literals
            "address",
            "boolean",
            "field",
            "group",
            "i8",
            "i16",
            "i32",
            "i64",
            "i128",
            "u8",
            "u16",
            "u32",
            "u64",
            "u128",
            "scalar",
            "string",
            // Boolean
            "true",
            "false",
            // Statements
            "input",
            "output",
            "as",
            "into",
            // Reserved (catch all)
            "function",
            "interface",
            "record",
        ];
        // Convert the given name to a string.
        let name = name.to_string();
        // Check if the name is a keyword.
        KEYWORDS.iter().any(|keyword| *keyword == &name)
    }
}

impl<N: Network> Parser for Program<N> {
    /// Parses a string into a program.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // A helper to parse a program.
        enum P<N: Network> {
            I(Interface<N>),
            R(RecordType<N>),
            F(Function<N>),
        }

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the interface or function from the string.
        let (string, components) = many1(alt((
            map(Interface::parse, |interface| P::<N>::I(interface)),
            map(RecordType::parse, |record| P::<N>::R(record)),
            map(Function::parse, |function| P::<N>::F(function)),
        )))(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;

        // Return the program.
        map_res(take(0usize), move |_| {
            // Initialize a new program.
            let mut program = Program::<N>::new();
            // Construct the program with the parsed components.
            for component in components.iter() {
                match component {
                    P::I(interface) => program.add_interface(interface.clone())?,
                    P::R(record) => program.add_record(record.clone())?,
                    P::F(function) => program.add_function(function.clone())?,
                }
            }
            // Output the program.
            Ok::<_, Error>(program)
        })(string)
    }
}

impl<N: Network> FromStr for Program<N> {
    type Err = Error;

    /// Returns a program from a string literal.
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Remaining invalid string is: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for Program<N> {
    /// Prints the program as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Program<N> {
    /// Prints the program as a string.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Initialize a string for the program.
        let mut program = String::new();

        for (identifier, definition) in self.identifiers.iter() {
            match definition {
                ProgramDefinition::Interface => match self.interfaces.get(identifier) {
                    Some(interface) => program.push_str(&format!("{interface}\n\n")),
                    None => {
                        eprintln!("'{}' is not defined.", identifier);
                        return Err(fmt::Error);
                    }
                },
                ProgramDefinition::Record => match self.records.get(identifier) {
                    Some(record) => program.push_str(&format!("{record}\n\n")),
                    None => {
                        eprintln!("'{}' is not defined.", identifier);
                        return Err(fmt::Error);
                    }
                },
                ProgramDefinition::Function => match self.functions.get(identifier) {
                    Some(function) => program.push_str(&format!("{function}\n\n")),
                    None => {
                        eprintln!("'{}' is not defined.", identifier);
                        return Err(fmt::Error);
                    }
                },
            }
        }
        // Remove the last newline.
        program.pop();

        write!(f, "{program}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_program_interface() -> Result<()> {
        // Create a new interface.
        let interface = Interface::<CurrentNetwork>::from_str(
            r"
interface message:
    first as field;
    second as field;",
        )?;

        // Initialize a new program.
        let mut program = Program::<CurrentNetwork>::new();

        // Add the interface to the program.
        program.add_interface(interface.clone())?;
        // Ensure the interface was added.
        assert!(program.contains_interface(&Identifier::from_str("message")?));
        // Ensure the retrieved interface matches.
        assert_eq!(interface, program.get_interface(&Identifier::from_str("message")?)?);

        Ok(())
    }

    #[test]
    fn test_program_record() -> Result<()> {
        // Create a new record.
        let record = RecordType::<CurrentNetwork>::from_str(
            r"
record foo:
    first as field.private;
    second as field.public;",
        )?;

        // Initialize a new program.
        let mut program = Program::<CurrentNetwork>::new();

        // Add the record to the program.
        program.add_record(record.clone())?;
        // Ensure the record was added.
        assert!(program.contains_record(&Identifier::from_str("foo")?));
        // Ensure the retrieved record matches.
        assert_eq!(record, program.get_record(&Identifier::from_str("foo")?)?);

        Ok(())
    }

    #[test]
    fn test_program_function() -> Result<()> {
        // Create a new function.
        let function = Function::<CurrentNetwork>::from_str(
            r"
function compute:
    input r0 as field.public;
    input r1 as field.private;
    add r0 r1 into r2;
    output r2 as field.private;",
        )?;

        // Initialize a new program.
        let mut program = Program::<CurrentNetwork>::new();

        // Add the function to the program.
        program.add_function(function.clone())?;
        // Ensure the function was added.
        assert!(program.contains_function(&Identifier::from_str("compute")?));
        // Ensure the retrieved function matches.
        assert_eq!(function, program.get_function(&Identifier::from_str("compute")?)?);

        Ok(())
    }

    #[test]
    fn test_program_parse() -> Result<()> {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
interface message:
    first as field;
    second as field;

function compute:
    input r0 as message.private;
    add r0.first r0.second into r1;
    output r1 as field.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Ensure the program contains the interface.
        assert!(program.contains_interface(&Identifier::from_str("message")?));
        // Ensure the program contains the function.
        assert!(program.contains_function(&Identifier::from_str("compute")?));

        // Retrieve the `compute` function.
        let compute = program.get_function(&Identifier::from_str("compute")?)?;

        // // Declare the input value.
        // let input = Value::from_str("{ 2field.public, 3field.private }");
        //
        // // Declare the expected output value.
        // let expected = Value::from_str("5field.private");
        //
        // // Compute the output value.
        // let output = compute.evaluate(&[input]);
        // assert_eq!(1, output.len());
        // assert_eq!(expected, output[0]);
        Ok(())
    }

    #[test]
    fn test_program_display() -> Result<()> {
        let expected = r"interface message:
    first as field;
    second as field;

function compute:
    input r0 as message.private;
    add r0.first r0.second into r1;
    output r1 as field.private;
";
        // Parse a new program.
        let program = Program::<CurrentNetwork>::from_str(expected)?;
        // Ensure the program string matches.
        assert_eq!(expected, format!("{program}"));

        Ok(())
    }
}
