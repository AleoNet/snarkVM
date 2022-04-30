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

use crate::{Definition, Function, Identifier, Program, Sanitizer};
use snarkvm_circuits::{prelude::*, Devnet};

use indexmap::IndexMap;
use std::cell::RefCell;

thread_local! {
    /// The definitions declared for the process.
    /// This is a map from the definition name to the definition.
    static DEFINITIONS: RefCell<IndexMap<Identifier<Process>, Definition<Process>>> = Default::default();
    /// The functions declared for the process.
    /// This is a map from the function name to the function.
    static FUNCTIONS: RefCell<IndexMap<Identifier<Process>, Function<Process>>> = Default::default();
}

/// A process is a threaded-instance of a program. This design paradigm is used to allow for
/// the re-execution of a program, and to allow for multiple programs to be run concurrently.
#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, Hash)]
pub struct Process;

impl Program for Process {
    type Aleo = Devnet;

    /// Adds a new definition to the process.
    ///
    /// # Errors
    /// This method will halt if the definition was previously added.
    #[inline]
    fn new_definition(definition: Definition<Self>) {
        DEFINITIONS.with(|definitions| {
            // Add the definition to the map.
            // Ensure the definition was not previously added.
            let name = definition.name().clone();
            if let Some(..) = definitions.borrow_mut().insert(name.clone(), definition) {
                Self::halt(format!("Definition \'{name}\' was previously added"))
            }
        });
    }

    /// Adds a new function to the process.
    ///
    /// # Errors
    /// This method will halt if the function was previously added.
    #[inline]
    fn new_function(function: Function<Self>) {
        FUNCTIONS.with(|functions| {
            // Add the function to the map.
            // Ensure the function was not previously added.
            let name = function.name().clone();
            if let Some(..) = functions.borrow_mut().insert(name.clone(), function) {
                Self::halt(format!("Function \'{name}\' was previously added"))
            }
        });
    }

    /// Returns `true` if the process contains a definition with the given name.
    fn contains_definition(name: &Identifier<Self>) -> bool {
        DEFINITIONS.with(|definitions| definitions.borrow().contains_key(name))
    }

    /// Returns `true` if the process contains a function with the given name.
    fn contains_function(name: &Identifier<Self>) -> bool {
        FUNCTIONS.with(|functions| functions.borrow().contains_key(name))
    }

    /// Returns the definition with the given name.
    fn get_definition(name: &Identifier<Self>) -> Option<Definition<Self>> {
        DEFINITIONS.with(|definitions| definitions.borrow().get(name).cloned())
    }

    /// Returns the function with the given name.
    fn get_function(name: &Identifier<Self>) -> Option<Function<Self>> {
        FUNCTIONS.with(|functions| functions.borrow().get(name).cloned())
    }
}

impl Parser for Process {
    type Environment = <Self as Program>::Aleo;

    /// Parses a string into a program.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the definition or function from the string.
        let (string, _) = many1(alt((
            map(Definition::parse, Self::new_definition),
            map(Function::parse, Self::new_function),
        )))(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        Ok((string, Self))
    }
}

impl fmt::Display for Process {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Initialize a string for the program.
        let mut program = String::new();

        // Write the definitions.
        DEFINITIONS.with(|definitions| {
            definitions.borrow().values().for_each(|definition| {
                program.push_str(definition.to_string().as_str());
                program.push('\n');
                program.push('\n');
            });
        });

        // Write the functions.
        FUNCTIONS.with(|functions| {
            functions.borrow().values().for_each(|function| {
                program.push_str(function.to_string().as_str());
                program.push('\n');
                program.push('\n');
            });
        });

        // Remove the penultimate newline.
        program.pop();
        // Remove the last newline.
        program.pop();

        write!(f, "{}", program)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Value;

    #[test]
    fn test_process_definition() {
        // Create a new definition.
        let definition = Definition::<Process>::from_str(
            r"
type message:
    first as field.public;
    second as field.private;",
        );

        // Add the definition to the process.
        Process::new_definition(definition.clone());

        // Ensure the definition was added.
        assert!(Process::contains_definition(&Identifier::from_str("message")));

        // Ensure the retrieved definition matches.
        assert_eq!(Some(definition), Process::get_definition(&Identifier::from_str("message")),);
    }

    #[test]
    fn test_process_function() {
        // Create a new function.
        let function = Function::<Process>::from_str(
            r"
function compute:
    input r0 as field.public;
    input r1 as field.private;
    add r0 r1 into r2;
    output r2 as field.private;",
        );

        // Add the function to the process.
        Process::new_function(function);

        // Ensure the function was added.
        assert!(Process::contains_function(&Identifier::from_str("compute")));
    }

    #[test]
    fn test_process_parse() {
        // Create a new program.
        Process::parse(
            r"
type message:
    first as field.public;
    second as field.private;

function compute:
    input r0 as message;
    add r0.first r0.second into r1;
    output r1 as field.private;",
        )
        .unwrap();

        // Ensure the program contains the definition.
        assert!(Process::contains_definition(&Identifier::from_str("message")));

        // Ensure the program contains the function.
        assert!(Process::contains_function(&Identifier::from_str("compute")));

        // Retrieve the `compute` function.
        let compute = Process::get_function(&Identifier::from_str("compute")).unwrap();

        // Declare the input value.
        let input = Value::from_str("message 2field.public 3field.private");

        // Declare the expected output value.
        let expected = Value::from_str("5field.private");

        // Compute the output value.
        let output = compute.evaluate(&[input]);
        assert_eq!(1, output.len());
        assert_eq!(expected, output[0]);
    }

    #[test]
    fn test_process_display() {
        // Create a new program.
        let expected = r"type message:
    first as field.public;
    second as field.private;

function compute:
    input r0 as message;
    add r0.first r0.second into r1;
    output r1 as field.private;";
        // Parse the program.
        Process::from_str(expected);
        // Print the program.
        assert_eq!(expected, format!("{Process}"));
    }
}
