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

impl<N: Network> Parser for Program<N> {
    /// Parses a string into a program.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // A helper to parse a program.
        enum P<N: Network> {
            I(Interface<N>),
            R(RecordType<N>),
            C(Closure<N>),
            F(Function<N>),
        }

        // Parse the imports from the string.
        let (string, imports) = many0(Import::parse)(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'program' keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the program ID from the string.
        let (string, id) = ProgramID::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the semicolon ';' keyword from the string.
        let (string, _) = tag(";")(string)?;

        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the interface or function from the string.
        let (string, components) = many1(alt((
            map(Interface::parse, |interface| P::<N>::I(interface)),
            map(RecordType::parse, |record| P::<N>::R(record)),
            map(Closure::parse, |closure| P::<N>::C(closure)),
            map(Function::parse, |function| P::<N>::F(function)),
        )))(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;

        // Return the program.
        map_res(take(0usize), move |_| {
            // Initialize a new program.
            let mut program = match Program::<N>::new(id) {
                Ok(program) => program,
                Err(error) => {
                    eprintln!("{error}");
                    return Err(error);
                }
            };
            // Construct the program with the parsed components.
            for component in components.iter() {
                let result = match component {
                    P::I(interface) => program.add_interface(interface.clone()),
                    P::R(record) => program.add_record(record.clone()),
                    P::C(closure) => program.add_closure(closure.clone()),
                    P::F(function) => program.add_function(function.clone()),
                };

                match result {
                    Ok(_) => (),
                    Err(error) => {
                        eprintln!("{error}");
                        return Err(error);
                    }
                }
            }
            // Lastly, add the imports (if any) to the program.
            for import in imports.iter() {
                match program.add_import(import.clone()) {
                    Ok(_) => (),
                    Err(error) => {
                        eprintln!("{error}");
                        return Err(error);
                    }
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

#[allow(clippy::format_push_string)]
impl<N: Network> Display for Program<N> {
    /// Prints the program as a string.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Initialize a string for the program.
        let mut program = String::new();

        if !self.imports.is_empty() {
            // Print the imports.
            for import in self.imports.values() {
                program.push_str(&format!("{}\n", import));
            }

            // Print a newline.
            program.push('\n');
        }

        // Print the program name.
        program += &format!("{} {};\n\n", Self::type_name(), self.id);

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
                ProgramDefinition::Closure => match self.closures.get(identifier) {
                    Some(closure) => program.push_str(&format!("{closure}\n\n")),
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
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_program_parse() -> Result<()> {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program to_parse.aleo;

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

        Ok(())
    }

    #[test]
    fn test_program_display() -> Result<()> {
        let expected = r"program to_parse.aleo;

interface message:
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
