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

use crate::{Function, Identifier, Interface, PlaintextType, RecordType};
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
                PlaintextType::Interface(identifier) => {
                    if !self.interfaces.contains_key(identifier) {
                        bail!("'{identifier}' in interface '{}' is not defined.", interface_name)
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
    #[inline]
    fn add_function(&mut self, function: Function<N>) -> Result<()> {
        // Retrieve the function name.
        let function_name = function.name().clone();

        // Ensure the function name is new.
        ensure!(self.is_unique_name(&function_name), "'{}' is already in use.", function_name);
        // Ensure the function name is not a reserved keyword.
        ensure!(!self.is_reserved_name(&function_name), "'{}' is a reserved keyword.", function_name);

        // // Ensure all interface members are well-formed.
        // // Note: This design ensures cyclic references are not possible.
        // for (identifier, plaintext_type) in function.members() {
        //     // Ensure the member name is not a reserved keyword.
        //     ensure!(self.is_reserved_name(identifier), "'{identifier}' is a reserved keyword.");
        //     // Ensure the member type is already defined in the program.
        //     match plaintext_type {
        //         PlaintextType::Literal(..) => continue,
        //         PlaintextType::Interface(identifier) => {
        //             if !self.interfaces.contains_key(identifier) {
        //                 bail!("'{identifier}' in interface '{}' is not defined.", interface_name)
        //             }
        //         }
        //     }
        // }

        // Add the function name to the identifiers.
        if self.identifiers.insert(function_name.clone(), ProgramDefinition::Function).is_some() {
            bail!("'{}' already exists in the program.", function_name)
        }
        // Add the function to the program.
        if self.functions.insert(function_name.clone(), function).is_some() {
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
    pub fn get_interface(&self, name: &Identifier<N>) -> Option<Interface<N>> {
        self.interfaces.get(name).cloned()
    }

    /// Returns the record with the given name.
    pub fn get_record(&self, name: &Identifier<N>) -> Option<RecordType<N>> {
        self.records.get(name).cloned()
    }

    /// Returns the function with the given name.
    pub fn get_function(&self, name: &Identifier<N>) -> Option<Function<N>> {
        self.functions.get(name).cloned()
    }
}

impl<N: Network> Program<N> {
    /// Returns `true` if the given name does not already exist in the program.
    fn is_unique_name(&self, name: &Identifier<N>) -> bool {
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
        assert_eq!(Some(interface), program.get_interface(&Identifier::from_str("message")?));

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
        assert_eq!(Some(function), program.get_function(&Identifier::from_str("compute")?));

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
        let compute = program.get_function(&Identifier::from_str("compute")?).unwrap();

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
    output r1 as field.private;";
        // Parse a new program.
        let program = Program::<CurrentNetwork>::from_str(expected)?;
        // Ensure the program string matches.
        assert_eq!(expected, format!("{program}"));

        Ok(())
    }
}
