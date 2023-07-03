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

use super::*;

impl<N: Network, Instruction: InstructionTrait<N>, Command: CommandTrait<N>> Parser
    for ProgramCore<N, Instruction, Command>
{
    /// Parses a string into a program.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // A helper to parse a program.
        enum P<N: Network, Instruction: InstructionTrait<N>, Command: CommandTrait<N>> {
            M(Mapping<N>),
            I(Struct<N>),
            R(RecordType<N>),
            C(ClosureCore<N, Instruction>),
            F(FunctionCore<N, Instruction, Command>),
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

        // Parse the struct or function from the string.
        let (string, components) = many1(alt((
            map(Mapping::parse, |mapping| P::<N, Instruction, Command>::M(mapping)),
            map(Struct::parse, |struct_| P::<N, Instruction, Command>::I(struct_)),
            map(RecordType::parse, |record| P::<N, Instruction, Command>::R(record)),
            map(ClosureCore::parse, |closure| P::<N, Instruction, Command>::C(closure)),
            map(FunctionCore::parse, |function| P::<N, Instruction, Command>::F(function)),
        )))(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;

        // Return the program.
        map_res(take(0usize), move |_| {
            // Initialize a new program.
            let mut program = match ProgramCore::<N, Instruction, Command>::new(id) {
                Ok(program) => program,
                Err(error) => {
                    eprintln!("{error}");
                    return Err(error);
                }
            };
            // Construct the program with the parsed components.
            for component in components.iter() {
                let result = match component {
                    P::M(mapping) => program.add_mapping(mapping.clone()),
                    P::I(struct_) => program.add_struct(struct_.clone()),
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

impl<N: Network, Instruction: InstructionTrait<N>, Command: CommandTrait<N>> FromStr
    for ProgramCore<N, Instruction, Command>
{
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

impl<N: Network, Instruction: InstructionTrait<N>, Command: CommandTrait<N>> Debug
    for ProgramCore<N, Instruction, Command>
{
    /// Prints the program as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[allow(clippy::format_push_string)]
impl<N: Network, Instruction: InstructionTrait<N>, Command: CommandTrait<N>> Display
    for ProgramCore<N, Instruction, Command>
{
    /// Prints the program as a string.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Initialize a string for the program.
        let mut program = String::new();

        if !self.imports.is_empty() {
            // Print the imports.
            for import in self.imports.values() {
                program.push_str(&format!("{import}\n"));
            }

            // Print a newline.
            program.push('\n');
        }

        // Print the program name.
        program += &format!("{} {};\n\n", Self::type_name(), self.id);

        for (identifier, definition) in self.identifiers.iter() {
            match definition {
                ProgramDefinition::Mapping => match self.mappings.get(identifier) {
                    Some(mapping) => program.push_str(&format!("{mapping}\n\n")),
                    None => return Err(fmt::Error),
                },
                ProgramDefinition::Struct => match self.structs.get(identifier) {
                    Some(struct_) => program.push_str(&format!("{struct_}\n\n")),
                    None => return Err(fmt::Error),
                },
                ProgramDefinition::Record => match self.records.get(identifier) {
                    Some(record) => program.push_str(&format!("{record}\n\n")),
                    None => return Err(fmt::Error),
                },
                ProgramDefinition::Closure => match self.closures.get(identifier) {
                    Some(closure) => program.push_str(&format!("{closure}\n\n")),
                    None => return Err(fmt::Error),
                },
                ProgramDefinition::Function => match self.functions.get(identifier) {
                    Some(function) => program.push_str(&format!("{function}\n\n")),
                    None => return Err(fmt::Error),
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
    use crate::Program;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_program_parse() -> Result<()> {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program to_parse.aleo;

struct message:
    first as field;
    second as field;

function compute:
    input r0 as message.private;
    add r0.first r0.second into r1;
    output r1 as field.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Ensure the program contains the struct.
        assert!(program.contains_struct(&Identifier::from_str("message")?));
        // Ensure the program contains the function.
        assert!(program.contains_function(&Identifier::from_str("compute")?));

        Ok(())
    }

    #[test]
    fn test_program_parse_function_zero_inputs() -> Result<()> {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program to_parse.aleo;

function compute:
    add 1u32 2u32 into r0;
    output r0 as u32.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Ensure the program contains the function.
        assert!(program.contains_function(&Identifier::from_str("compute")?));

        Ok(())
    }

    #[test]
    fn test_program_display() -> Result<()> {
        let expected = r"program to_parse.aleo;

struct message:
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
