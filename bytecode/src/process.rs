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
            map(Definition::parse, |definition| Self::new_definition(definition)),
            map(Function::parse, |function| Self::new_function(function)),
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
            });
        });

        // Write the functions.
        FUNCTIONS.with(|functions| {
            functions.borrow().values().for_each(|function| {
                program.push_str(function.to_string().as_str());
                program.push('\n');
            });
        });

        // Remove the last newline.
        program.pop();

        write!(f, "{}", program)
    }
}
