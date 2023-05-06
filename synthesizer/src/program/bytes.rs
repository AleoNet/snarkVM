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

impl<N: Network> FromBytes for Program<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u8::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid program version"));
        }

        // Read the program ID.
        let id = ProgramID::read_le(&mut reader)?;

        // Initialize the program.
        let mut program = Program::new(id).map_err(|e| error(e.to_string()))?;

        // Read the number of program imports.
        let imports_len = u8::read_le(&mut reader)?;
        // Read the program imports.
        for _ in 0..imports_len {
            program.add_import(Import::read_le(&mut reader)?).map_err(|e| error(e.to_string()))?;
        }

        // Read the number of components.
        let components_len = u16::read_le(&mut reader)?;
        for _ in 0..components_len {
            // Read the variant.
            let variant = u8::read_le(&mut reader)?;
            // Match the variant.
            match variant {
                // Read the mapping.
                0 => program.add_mapping(Mapping::read_le(&mut reader)?).map_err(|e| error(e.to_string()))?,
                // Read the struct.
                1 => program.add_struct(Struct::read_le(&mut reader)?).map_err(|e| error(e.to_string()))?,
                // Read the record.
                2 => program.add_record(RecordType::read_le(&mut reader)?).map_err(|e| error(e.to_string()))?,
                // Read the closure.
                3 => program.add_closure(Closure::read_le(&mut reader)?).map_err(|e| error(e.to_string()))?,
                // Read the function.
                4 => program.add_function(Function::read_le(&mut reader)?).map_err(|e| error(e.to_string()))?,
                // Invalid variant.
                _ => return Err(error(format!("Failed to parse program. Invalid component variant '{variant}'"))),
            }
        }

        Ok(program)
    }
}

impl<N: Network> ToBytes for Program<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u8.write_le(&mut writer)?;

        // Write the program ID.
        self.id.write_le(&mut writer)?;

        // Write the number of program imports.
        (self.imports.len() as u8).write_le(&mut writer)?;
        // Write the program imports.
        for import in self.imports.values() {
            import.write_le(&mut writer)?;
        }

        // Write the number of components.
        (self.identifiers.len() as u16).write_le(&mut writer)?;
        // Write the components.
        for (identifier, definition) in self.identifiers.iter() {
            match definition {
                ProgramDefinition::Mapping => match self.mappings.get(identifier) {
                    Some(mapping) => {
                        // Write the variant.
                        0u8.write_le(&mut writer)?;
                        // Write the mapping.
                        mapping.write_le(&mut writer)?;
                    }
                    None => return Err(error(format!("Mapping '{identifier}' is not defined"))),
                },
                ProgramDefinition::Struct => match self.structs.get(identifier) {
                    Some(struct_) => {
                        // Write the variant.
                        1u8.write_le(&mut writer)?;
                        // Write the struct.
                        struct_.write_le(&mut writer)?;
                    }
                    None => return Err(error(format!("Struct '{identifier}' is not defined."))),
                },
                ProgramDefinition::Record => match self.records.get(identifier) {
                    Some(record) => {
                        // Write the variant.
                        2u8.write_le(&mut writer)?;
                        // Write the record.
                        record.write_le(&mut writer)?;
                    }
                    None => return Err(error(format!("Record '{identifier}' is not defined."))),
                },
                ProgramDefinition::Closure => match self.closures.get(identifier) {
                    Some(closure) => {
                        // Write the variant.
                        3u8.write_le(&mut writer)?;
                        // Write the closure.
                        closure.write_le(&mut writer)?;
                    }
                    None => return Err(error(format!("Closure '{identifier}' is not defined."))),
                },
                ProgramDefinition::Function => match self.functions.get(identifier) {
                    Some(function) => {
                        // Write the variant.
                        4u8.write_le(&mut writer)?;
                        // Write the function.
                        function.write_le(&mut writer)?;
                    }
                    None => return Err(error(format!("Function '{identifier}' is not defined."))),
                },
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() -> Result<()> {
        let program = r"
program token.aleo;

record token:
    owner as address.private;
    token_amount as u64.private;

function compute:
    input r0 as token.record;
    add r0.token_amount r0.token_amount into r1;
    output r1 as u64.private;";

        // Initialize a new program.
        let (string, expected) = Program::<CurrentNetwork>::parse(program).unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        let expected_bytes = expected.to_bytes_le()?;

        let candidate = Program::<CurrentNetwork>::from_bytes_le(&expected_bytes)?;
        assert_eq!(expected, candidate);
        assert_eq!(expected_bytes, candidate.to_bytes_le()?);

        Ok(())
    }
}
