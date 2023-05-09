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

mod closure;
pub use closure::*;

pub mod finalize;

mod function;
pub use function::*;

mod import;
pub use import::*;

mod instruction;
pub use instruction::*;

mod mapping;
pub use mapping::*;

mod bytes;
mod parse;
mod serialize;

use console::{
    network::prelude::*,
    program::{EntryType, Identifier, PlaintextType, ProgramID, RecordType, Struct},
};

use indexmap::IndexMap;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum ProgramDefinition {
    /// A program mapping.
    Mapping,
    /// A program struct.
    Struct,
    /// A program record.
    Record,
    /// A program closure.
    Closure,
    /// A program function.
    Function,
}

#[derive(Clone, PartialEq, Eq)]
pub struct Program<N: Network> {
    /// The ID of the program.
    id: ProgramID<N>,
    /// A map of the declared imports for the program.
    imports: IndexMap<ProgramID<N>, Import<N>>,
    /// A map of identifiers to their program declaration.
    identifiers: IndexMap<Identifier<N>, ProgramDefinition>,
    /// A map of the declared mappings for the program.
    mappings: IndexMap<Identifier<N>, Mapping<N>>,
    /// A map of the declared structs for the program.
    structs: IndexMap<Identifier<N>, Struct<N>>,
    /// A map of the declared record types for the program.
    records: IndexMap<Identifier<N>, RecordType<N>>,
    /// A map of the declared closures for the program.
    closures: IndexMap<Identifier<N>, Closure<N>>,
    /// A map of the declared functions for the program.
    functions: IndexMap<Identifier<N>, Function<N>>,
}

impl<N: Network> Program<N> {
    /// Initializes an empty program.
    #[inline]
    pub fn new(id: ProgramID<N>) -> Result<Self> {
        // Ensure the program name is valid.
        ensure!(!Self::is_reserved_keyword(id.name()), "Program name is invalid: {}", id.name());
        // Ensure the program network-level domain is `aleo`.
        ensure!(id.is_aleo(), "Program network is invalid: {}", id.network());

        Ok(Self {
            id,
            imports: IndexMap::new(),
            identifiers: IndexMap::new(),
            mappings: IndexMap::new(),
            structs: IndexMap::new(),
            records: IndexMap::new(),
            closures: IndexMap::new(),
            functions: IndexMap::new(),
        })
    }

    /// Initializes the credits program.
    #[inline]
    pub fn credits() -> Result<Self> {
        Self::from_str(
            r"
program credits.aleo;

record credits:
    owner as address.private;
    microcredits as u64.private;

function mint:
    input r0 as address.public;
    input r1 as u64.public;
    cast r0 r1 into r2 as credits.record;
    output r2 as credits.record;

function transfer:
    input r0 as credits.record;
    input r1 as address.private;
    input r2 as u64.private;
    sub r0.microcredits r2 into r3;
    cast r1 r2 into r4 as credits.record;
    cast r0.owner r3 into r5 as credits.record;
    output r4 as credits.record;
    output r5 as credits.record;

function join:
    input r0 as credits.record;
    input r1 as credits.record;
    add r0.microcredits r1.microcredits into r2;
    cast r0.owner r2 into r3 as credits.record;
    output r3 as credits.record;

function split:
    input r0 as credits.record;
    input r1 as u64.private;
    sub r0.microcredits r1 into r2;
    cast r0.owner r1 into r3 as credits.record;
    cast r0.owner r2 into r4 as credits.record;
    output r3 as credits.record;
    output r4 as credits.record;

function fee:
    input r0 as credits.record;
    input r1 as u64.public;
    assert.neq r1 0u64;
    sub r0.microcredits r1 into r2;
    cast r0.owner r2 into r3 as credits.record;
    output r3 as credits.record;
",
        )
    }

    /// Returns the ID of the program.
    pub const fn id(&self) -> &ProgramID<N> {
        &self.id
    }

    /// Returns the imports in the program.
    pub const fn imports(&self) -> &IndexMap<ProgramID<N>, Import<N>> {
        &self.imports
    }

    /// Returns the mappings in the program.
    pub const fn mappings(&self) -> &IndexMap<Identifier<N>, Mapping<N>> {
        &self.mappings
    }

    /// Returns the closures in the program.
    pub const fn closures(&self) -> &IndexMap<Identifier<N>, Closure<N>> {
        &self.closures
    }

    /// Returns the functions in the program.
    pub const fn functions(&self) -> &IndexMap<Identifier<N>, Function<N>> {
        &self.functions
    }

    /// Returns `true` if the program contains an import with the given program ID.
    pub fn contains_import(&self, id: &ProgramID<N>) -> bool {
        self.imports.contains_key(id)
    }

    /// Returns `true` if the program contains a mapping with the given name.
    pub fn contains_mapping(&self, name: &Identifier<N>) -> bool {
        self.mappings.contains_key(name)
    }

    /// Returns `true` if the program contains a struct with the given name.
    pub fn contains_struct(&self, name: &Identifier<N>) -> bool {
        self.structs.contains_key(name)
    }

    /// Returns `true` if the program contains a record with the given name.
    pub fn contains_record(&self, name: &Identifier<N>) -> bool {
        self.records.contains_key(name)
    }

    /// Returns `true` if the program contains a closure with the given name.
    pub fn contains_closure(&self, name: &Identifier<N>) -> bool {
        self.closures.contains_key(name)
    }

    /// Returns `true` if the program contains a function with the given name.
    pub fn contains_function(&self, name: &Identifier<N>) -> bool {
        self.functions.contains_key(name)
    }

    /// Returns the mapping with the given name.
    pub fn get_mapping(&self, name: &Identifier<N>) -> Result<Mapping<N>> {
        // Attempt to retrieve the mapping.
        let mapping = self.mappings.get(name).cloned().ok_or_else(|| anyhow!("Mapping '{name}' is not defined."))?;
        // Ensure the mapping name matches.
        ensure!(mapping.name() == name, "Expected mapping '{name}', but found mapping '{}'", mapping.name());
        // Return the mapping.
        Ok(mapping)
    }

    /// Returns the struct with the given name.
    pub fn get_struct(&self, name: &Identifier<N>) -> Result<Struct<N>> {
        // Attempt to retrieve the struct.
        let struct_ = self.structs.get(name).cloned().ok_or_else(|| anyhow!("Struct '{name}' is not defined."))?;
        // Ensure the struct name matches.
        ensure!(struct_.name() == name, "Expected struct '{name}', but found struct '{}'", struct_.name());
        // Ensure the struct contains members.
        ensure!(!struct_.members().is_empty(), "Struct '{name}' is missing members.");
        // Return the struct.
        Ok(struct_)
    }

    /// Returns the record with the given name.
    pub fn get_record(&self, name: &Identifier<N>) -> Result<RecordType<N>> {
        // Attempt to retrieve the record.
        let record = self.records.get(name).cloned().ok_or_else(|| anyhow!("Record '{name}' is not defined."))?;
        // Ensure the record name matches.
        ensure!(record.name() == name, "Expected record '{name}', but found record '{}'", record.name());
        // Return the record.
        Ok(record)
    }

    /// Returns the closure with the given name.
    pub fn get_closure(&self, name: &Identifier<N>) -> Result<Closure<N>> {
        // Attempt to retrieve the closure.
        let closure = self.closures.get(name).cloned().ok_or_else(|| anyhow!("Closure '{name}' is not defined."))?;
        // Ensure the closure name matches.
        ensure!(closure.name() == name, "Expected closure '{name}', but found closure '{}'", closure.name());
        // Ensure there are input statements in the closure.
        ensure!(!closure.inputs().is_empty(), "Cannot evaluate a closure without input statements");
        // Ensure the number of inputs is within the allowed range.
        ensure!(closure.inputs().len() <= N::MAX_INPUTS, "Closure exceeds maximum number of inputs");
        // Ensure there are instructions in the closure.
        ensure!(!closure.instructions().is_empty(), "Cannot evaluate a closure without instructions");
        // Ensure the number of outputs is within the allowed range.
        ensure!(closure.outputs().len() <= N::MAX_OUTPUTS, "Closure exceeds maximum number of outputs");
        // Return the closure.
        Ok(closure)
    }

    /// Returns the function with the given name.
    pub fn get_function(&self, name: &Identifier<N>) -> Result<Function<N>> {
        // Attempt to retrieve the function.
        let function = self.functions.get(name).cloned().ok_or_else(|| anyhow!("Function '{name}' is not defined."))?;
        // Ensure the function name matches.
        ensure!(function.name() == name, "Expected function '{name}', but found function '{}'", function.name());
        // Ensure the number of inputs is within the allowed range.
        ensure!(function.inputs().len() <= N::MAX_INPUTS, "Function exceeds maximum number of inputs");
        // Ensure the number of instructions is within the allowed range.
        ensure!(function.instructions().len() <= N::MAX_INSTRUCTIONS, "Function exceeds maximum instructions");
        // Ensure the number of outputs is within the allowed range.
        ensure!(function.outputs().len() <= N::MAX_OUTPUTS, "Function exceeds maximum number of outputs");
        // Return the function.
        Ok(function)
    }
}

impl<N: Network> Program<N> {
    /// Adds a new import statement to the program.
    ///
    /// # Errors
    /// This method will halt if the imported program was previously added.
    #[inline]
    fn add_import(&mut self, import: Import<N>) -> Result<()> {
        // Retrieve the imported program name.
        let import_name = *import.name();

        // Ensure the import name is new.
        ensure!(self.is_unique_name(&import_name), "'{import_name}' is already in use.");
        // Ensure the import name is not a reserved opcode.
        ensure!(!Self::is_reserved_opcode(&import_name.to_string()), "'{import_name}' is a reserved opcode.");
        // Ensure the import name is not a reserved keyword.
        ensure!(!Self::is_reserved_keyword(&import_name), "'{import_name}' is a reserved keyword.");

        // Ensure the import is new.
        ensure!(
            !self.imports.contains_key(import.program_id()),
            "Import '{}' is already defined.",
            import.program_id()
        );

        // Add the import statement to the program.
        if self.imports.insert(*import.program_id(), import.clone()).is_some() {
            bail!("'{}' already exists in the program.", import.program_id())
        }
        Ok(())
    }

    /// Adds a new mapping to the program.
    ///
    /// # Errors
    /// This method will halt if the mapping name is already in use.
    /// This method will halt if the mapping name is a reserved opcode or keyword.
    #[inline]
    fn add_mapping(&mut self, mapping: Mapping<N>) -> Result<()> {
        // Retrieve the mapping name.
        let mapping_name = *mapping.name();

        // Ensure the program has not exceeded the maximum number of mappings.
        ensure!(self.mappings.len() < N::MAX_MAPPINGS, "Program exceeds the maximum number of mappings");

        // Ensure the mapping name is new.
        ensure!(self.is_unique_name(&mapping_name), "'{mapping_name}' is already in use.");
        // Ensure the mapping name is not a reserved keyword.
        ensure!(!Self::is_reserved_keyword(&mapping_name), "'{mapping_name}' is a reserved keyword.");
        // Ensure the mapping name is not a reserved opcode.
        ensure!(!Self::is_reserved_opcode(&mapping_name.to_string()), "'{mapping_name}' is a reserved opcode.");

        // Add the mapping name to the identifiers.
        if self.identifiers.insert(mapping_name, ProgramDefinition::Mapping).is_some() {
            bail!("'{mapping_name}' already exists in the program.")
        }
        // Add the mapping to the program.
        if self.mappings.insert(mapping_name, mapping).is_some() {
            bail!("'{mapping_name}' already exists in the program.")
        }
        Ok(())
    }

    /// Adds a new struct to the program.
    ///
    /// # Errors
    /// This method will halt if the struct was previously added.
    /// This method will halt if the struct name is already in use in the program.
    /// This method will halt if the struct name is a reserved opcode or keyword.
    /// This method will halt if any structs in the struct's members are not already defined.
    #[inline]
    fn add_struct(&mut self, struct_: Struct<N>) -> Result<()> {
        // Retrieve the struct name.
        let struct_name = *struct_.name();

        // Ensure the struct name is new.
        ensure!(self.is_unique_name(&struct_name), "'{struct_name}' is already in use.");
        // Ensure the struct name is not a reserved opcode.
        ensure!(!Self::is_reserved_opcode(&struct_name.to_string()), "'{struct_name}' is a reserved opcode.");
        // Ensure the struct name is not a reserved keyword.
        ensure!(!Self::is_reserved_keyword(&struct_name), "'{struct_name}' is a reserved keyword.");

        // Ensure the struct contains members.
        ensure!(!struct_.members().is_empty(), "Struct '{struct_name}' is missing members.");

        // Ensure all struct members are well-formed.
        // Note: This design ensures cyclic references are not possible.
        for (identifier, plaintext_type) in struct_.members() {
            // Ensure the member name is not a reserved keyword.
            ensure!(!Self::is_reserved_keyword(identifier), "'{identifier}' is a reserved keyword.");
            // Ensure the member type is already defined in the program.
            match plaintext_type {
                PlaintextType::Literal(..) => continue,
                PlaintextType::Struct(member_identifier) => {
                    // Ensure the member struct name exists in the program.
                    if !self.structs.contains_key(member_identifier) {
                        bail!("'{member_identifier}' in struct '{}' is not defined.", struct_name)
                    }
                }
            }
        }

        // Add the struct name to the identifiers.
        if self.identifiers.insert(struct_name, ProgramDefinition::Struct).is_some() {
            bail!("'{}' already exists in the program.", struct_name)
        }
        // Add the struct to the program.
        if self.structs.insert(struct_name, struct_).is_some() {
            bail!("'{}' already exists in the program.", struct_name)
        }
        Ok(())
    }

    /// Adds a new record to the program.
    ///
    /// # Errors
    /// This method will halt if the record was previously added.
    /// This method will halt if the record name is already in use in the program.
    /// This method will halt if the record name is a reserved opcode or keyword.
    /// This method will halt if any records in the record's members are not already defined.
    #[inline]
    fn add_record(&mut self, record: RecordType<N>) -> Result<()> {
        // Retrieve the record name.
        let record_name = *record.name();

        // Ensure the record name is new.
        ensure!(self.is_unique_name(&record_name), "'{record_name}' is already in use.");
        // Ensure the record name is not a reserved opcode.
        ensure!(!Self::is_reserved_opcode(&record_name.to_string()), "'{record_name}' is a reserved opcode.");
        // Ensure the record name is not a reserved keyword.
        ensure!(!Self::is_reserved_keyword(&record_name), "'{record_name}' is a reserved keyword.");

        // Ensure all record entries are well-formed.
        // Note: This design ensures cyclic references are not possible.
        for (identifier, entry_type) in record.entries() {
            // Ensure the member name is not a reserved keyword.
            ensure!(!Self::is_reserved_keyword(identifier), "'{identifier}' is a reserved keyword.");
            // Ensure the member type is already defined in the program.
            match entry_type {
                // Ensure the plaintext type is already defined.
                EntryType::Constant(plaintext_type)
                | EntryType::Public(plaintext_type)
                | EntryType::Private(plaintext_type) => match plaintext_type {
                    PlaintextType::Literal(..) => continue,
                    PlaintextType::Struct(identifier) => {
                        if !self.structs.contains_key(identifier) {
                            bail!("Struct '{identifier}' in record '{record_name}' is not defined.")
                        }
                    }
                },
            }
        }

        // Add the record name to the identifiers.
        if self.identifiers.insert(record_name, ProgramDefinition::Record).is_some() {
            bail!("'{record_name}' already exists in the program.")
        }
        // Add the record to the program.
        if self.records.insert(record_name, record).is_some() {
            bail!("'{record_name}' already exists in the program.")
        }
        Ok(())
    }

    /// Adds a new closure to the program.
    ///
    /// # Errors
    /// This method will halt if the closure was previously added.
    /// This method will halt if the closure name is already in use in the program.
    /// This method will halt if the closure name is a reserved opcode or keyword.
    /// This method will halt if any registers are assigned more than once.
    /// This method will halt if the registers are not incrementing monotonically.
    /// This method will halt if an input type references a non-existent definition.
    /// This method will halt if an operand register does not already exist in memory.
    /// This method will halt if a destination register already exists in memory.
    /// This method will halt if an output register does not already exist.
    /// This method will halt if an output type references a non-existent definition.
    #[inline]
    fn add_closure(&mut self, closure: Closure<N>) -> Result<()> {
        // Retrieve the closure name.
        let closure_name = *closure.name();

        // Ensure the closure name is new.
        ensure!(self.is_unique_name(&closure_name), "'{closure_name}' is already in use.");
        // Ensure the closure name is not a reserved opcode.
        ensure!(!Self::is_reserved_opcode(&closure_name.to_string()), "'{closure_name}' is a reserved opcode.");
        // Ensure the closure name is not a reserved keyword.
        ensure!(!Self::is_reserved_keyword(&closure_name), "'{closure_name}' is a reserved keyword.");

        // Ensure there are input statements in the closure.
        ensure!(!closure.inputs().is_empty(), "Cannot evaluate a closure without input statements");
        // Ensure the number of inputs is within the allowed range.
        ensure!(closure.inputs().len() <= N::MAX_INPUTS, "Closure exceeds maximum number of inputs");
        // Ensure there are instructions in the closure.
        ensure!(!closure.instructions().is_empty(), "Cannot evaluate a closure without instructions");
        // Ensure the number of outputs is within the allowed range.
        ensure!(closure.outputs().len() <= N::MAX_OUTPUTS, "Closure exceeds maximum number of outputs");

        // Add the function name to the identifiers.
        if self.identifiers.insert(closure_name, ProgramDefinition::Closure).is_some() {
            bail!("'{closure_name}' already exists in the program.")
        }
        // Add the closure to the program.
        if self.closures.insert(closure_name, closure).is_some() {
            bail!("'{closure_name}' already exists in the program.")
        }
        Ok(())
    }

    /// Adds a new function to the program.
    ///
    /// # Errors
    /// This method will halt if the function was previously added.
    /// This method will halt if the function name is already in use in the program.
    /// This method will halt if the function name is a reserved opcode or keyword.
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
        let function_name = *function.name();

        // Ensure the program has not exceeded the maximum number of functions.
        ensure!(self.functions.len() < N::MAX_FUNCTIONS, "Program exceeds the maximum number of functions");

        // Ensure the function name is new.
        ensure!(self.is_unique_name(&function_name), "'{function_name}' is already in use.");
        // Ensure the function name is not a reserved opcode.
        ensure!(!Self::is_reserved_opcode(&function_name.to_string()), "'{function_name}' is a reserved opcode.");
        // Ensure the function name is not a reserved keyword.
        ensure!(!Self::is_reserved_keyword(&function_name), "'{function_name}' is a reserved keyword.");

        // Ensure the number of inputs is within the allowed range.
        ensure!(function.inputs().len() <= N::MAX_INPUTS, "Function exceeds maximum number of inputs");
        // Ensure the number of instructions is within the allowed range.
        ensure!(function.instructions().len() <= N::MAX_INSTRUCTIONS, "Function exceeds maximum instructions");
        // Ensure the number of outputs is within the allowed range.
        ensure!(function.outputs().len() <= N::MAX_OUTPUTS, "Function exceeds maximum number of outputs");

        // Add the function name to the identifiers.
        if self.identifiers.insert(function_name, ProgramDefinition::Function).is_some() {
            bail!("'{function_name}' already exists in the program.")
        }
        // Add the function to the program.
        if self.functions.insert(function_name, function).is_some() {
            bail!("'{function_name}' already exists in the program.")
        }
        Ok(())
    }
}

impl<N: Network> Program<N> {
    #[rustfmt::skip]
    const KEYWORDS: &'static [&'static str] = &[
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
        // Record
        "record",
        "owner",
        // Program
        "function",
        "struct",
        "closure",
        "program",
        "aleo",
        "self",
        "storage",
        "mapping",
        "key",
        "value",
        // Reserved (catch all)
        "global",
        "return",
        "break",
        "assert",
        "continue",
        "let",
        "if",
        "else",
        "while",
        "for",
        "switch",
        "case",
        "default",
        "match",
        "enum",
        "struct",
        "union",
        "trait",
        "impl",
        "type",
    ];

    /// Returns `true` if the given name does not already exist in the program.
    fn is_unique_name(&self, name: &Identifier<N>) -> bool {
        !self.identifiers.contains_key(name)
    }

    /// Returns `true` if the given name is a reserved opcode.
    pub fn is_reserved_opcode(name: &str) -> bool {
        // Check if the given name matches any opcode (in its entirety; including past the first '.' if it exists).
        Instruction::<N>::OPCODES.iter().any(|opcode| **opcode == name)
    }

    /// Returns `true` if the given name uses a reserved keyword.
    pub fn is_reserved_keyword(name: &Identifier<N>) -> bool {
        // Convert the given name to a string.
        let name = name.to_string();
        // Check if the name is a keyword.
        Self::KEYWORDS.iter().any(|keyword| *keyword == name)
    }
}

impl<N: Network> TypeName for Program<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "program"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CallStack, Execution, Inclusion};
    use circuit::network::AleoV0;
    use console::{
        account::{Address, PrivateKey},
        network::Testnet3,
        program::{Locator, Plaintext, Record, Value, ValueType},
        types::Field,
    };

    use parking_lot::RwLock;
    use std::sync::Arc;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    #[test]
    fn test_program_mapping() -> Result<()> {
        // Create a new mapping.
        let mapping = Mapping::<CurrentNetwork>::from_str(
            r"
mapping message:
    key first as field.public;
    value second as field.public;",
        )?;

        // Initialize a new program.
        let mut program = Program::<CurrentNetwork>::new(ProgramID::from_str("unknown.aleo")?)?;

        // Add the mapping to the program.
        program.add_mapping(mapping.clone())?;
        // Ensure the mapping was added.
        assert!(program.contains_mapping(&Identifier::from_str("message")?));
        // Ensure the retrieved mapping matches.
        assert_eq!(mapping, program.get_mapping(&Identifier::from_str("message")?)?);

        Ok(())
    }

    #[test]
    fn test_program_struct() -> Result<()> {
        // Create a new struct.
        let struct_ = Struct::<CurrentNetwork>::from_str(
            r"
struct message:
    first as field;
    second as field;",
        )?;

        // Initialize a new program.
        let mut program = Program::<CurrentNetwork>::new(ProgramID::from_str("unknown.aleo")?)?;

        // Add the struct to the program.
        program.add_struct(struct_.clone())?;
        // Ensure the struct was added.
        assert!(program.contains_struct(&Identifier::from_str("message")?));
        // Ensure the retrieved struct matches.
        assert_eq!(struct_, program.get_struct(&Identifier::from_str("message")?)?);

        Ok(())
    }

    #[test]
    fn test_program_record() -> Result<()> {
        // Create a new record.
        let record = RecordType::<CurrentNetwork>::from_str(
            r"
record foo:
    owner as address.private;
    first as field.private;
    second as field.public;",
        )?;

        // Initialize a new program.
        let mut program = Program::<CurrentNetwork>::new(ProgramID::from_str("unknown.aleo")?)?;

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
        let mut program = Program::<CurrentNetwork>::new(ProgramID::from_str("unknown.aleo")?)?;

        // Add the function to the program.
        program.add_function(function.clone())?;
        // Ensure the function was added.
        assert!(program.contains_function(&Identifier::from_str("compute")?));
        // Ensure the retrieved function matches.
        assert_eq!(function, program.get_function(&Identifier::from_str("compute")?)?);

        Ok(())
    }

    #[test]
    fn test_program_import() -> Result<()> {
        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r"
import eth.aleo;
import usdc.aleo;

program swap.aleo;

// The `swap` function transfers ownership of the record
// for token A to the record owner of token B, and vice-versa.
function swap:
    // Input the record for token A.
    input r0 as eth.aleo/eth.record;
    // Input the record for token B.
    input r1 as usdc.aleo/usdc.record;

    // Send the record for token A to the owner of token B.
    call eth.aleo/transfer r0 r1.owner r0.amount into r2 r3;

    // Send the record for token B to the owner of token A.
    call usdc.aleo/transfer r1 r0.owner r1.amount into r4 r5;

    // Output the new record for token A.
    output r2 as eth.aleo/eth.record;
    // Output the new record for token B.
    output r4 as usdc.aleo/usdc.record;
    ",
        )
        .unwrap();

        // Ensure the program imports exist.
        assert!(program.contains_import(&ProgramID::from_str("eth.aleo")?));
        assert!(program.contains_import(&ProgramID::from_str("usdc.aleo")?));

        // Retrieve the 'swap' function.
        let function = program.get_function(&Identifier::from_str("swap")?)?;

        // Ensure there are two inputs.
        assert_eq!(function.inputs().len(), 2);
        assert_eq!(function.input_types().len(), 2);

        // Ensure the inputs are external records.
        assert_eq!(function.input_types()[0], ValueType::ExternalRecord(Locator::from_str("eth.aleo/eth")?));
        assert_eq!(function.input_types()[1], ValueType::ExternalRecord(Locator::from_str("usdc.aleo/usdc")?));

        // Ensure there are two instructions.
        assert_eq!(function.instructions().len(), 2);

        // Ensure the instructions are calls.
        assert_eq!(function.instructions()[0].opcode(), Opcode::Call);
        assert_eq!(function.instructions()[1].opcode(), Opcode::Call);

        // Ensure there are two outputs.
        assert_eq!(function.outputs().len(), 2);
        assert_eq!(function.output_types().len(), 2);

        // Ensure the outputs are external records.
        assert_eq!(function.output_types()[0], ValueType::ExternalRecord(Locator::from_str("eth.aleo/eth")?));
        assert_eq!(function.output_types()[1], ValueType::ExternalRecord(Locator::from_str("usdc.aleo/usdc")?));

        Ok(())
    }

    #[test]
    fn test_program_evaluate_function() {
        let program = Program::<CurrentNetwork>::from_str(
            r"
    program example.aleo;

    function foo:
        input r0 as field.public;
        input r1 as field.private;
        add r0 r1 into r2;
        output r2 as field.private;
    ",
        )
        .unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("foo").unwrap();
        // Declare the function inputs.
        let inputs = [
            Value::<CurrentNetwork>::Plaintext(Plaintext::from_str("2field").unwrap()),
            Value::Plaintext(Plaintext::from_str("3field").unwrap()),
        ];

        // Construct the process.
        let process = crate::process::test_helpers::sample_process(&program);

        // Compute the authorization.
        let authorization = {
            // Initialize an RNG.
            let rng = &mut TestRng::default();

            // Initialize caller private key.
            let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

            // Authorize the function call.
            let authorization = process
                .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, inputs.iter(), rng)
                .unwrap();
            assert_eq!(authorization.len(), 1);
            authorization
        };

        // Retrieve the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Declare the expected output.
        let expected = Value::Plaintext(Plaintext::<CurrentNetwork>::from_str("5field").unwrap());

        // Run the function.
        let response =
            stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization.replicate()).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let response = stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }

    #[test]
    fn test_program_evaluate_struct_and_function() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program example.aleo;

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

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();
        // Declare the input value.
        let input =
            Value::<CurrentNetwork>::Plaintext(Plaintext::from_str("{ first: 2field, second: 3field }").unwrap());
        // Declare the expected output value.
        let expected = Value::Plaintext(Plaintext::from_str("5field").unwrap());

        // Construct the process.
        let process = crate::process::test_helpers::sample_process(&program);

        // Compute the authorization.
        let authorization = {
            // Initialize an RNG.
            let rng = &mut TestRng::default();

            // Initialize caller private key.
            let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

            // Authorize the function call.
            let authorization = process
                .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [input].iter(), rng)
                .unwrap();
            assert_eq!(authorization.len(), 1);
            authorization
        };

        // Retrieve the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Compute the output value.
        let response =
            stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization.replicate()).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let response = stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }

    #[test]
    fn test_program_evaluate_record_and_function() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

record token:
    owner as address.private;
    token_amount as u64.private;

function compute:
    input r0 as token.record;
    add r0.token_amount r0.token_amount into r1;
    output r1 as u64.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();

        // Initialize an RNG.
        let rng = &mut TestRng::default();

        // Initialize caller private key.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the input value.
        let input_record = Record::from_str(&format!(
            "{{ owner: {caller}.private, token_amount: 100u64.private, _nonce: 0group.public }}"
        ))
        .unwrap();
        let input = Value::<CurrentNetwork>::Record(input_record);

        // Declare the expected output value.
        let expected = Value::Plaintext(Plaintext::from_str("200u64").unwrap());

        // Construct the process.
        let process = crate::process::test_helpers::sample_process(&program);

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [input].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);

        // Retrieve the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Compute the output value.
        let response =
            stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization.replicate()).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let response = stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }

    #[test]
    fn test_program_evaluate_call() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program example_call.aleo;

// (a + (a + b)) + (a + b) == (3a + 2b)
closure execute:
    input r0 as field;
    input r1 as field;
    add r0 r1 into r2;
    add r0 r2 into r3;
    add r2 r3 into r4;
    output r4 as field;
    output r3 as field;
    output r2 as field;

function compute:
    input r0 as field.private;
    input r1 as field.public;
    call execute r0 r1 into r2 r3 r4;
    output r2 as field.private;
    output r3 as field.private;
    output r4 as field.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::Plaintext(Plaintext::from_str("3field").unwrap());
        let r1 = Value::<CurrentNetwork>::Plaintext(Plaintext::from_str("5field").unwrap());

        // Declare the expected output value.
        let r2 = Value::Plaintext(Plaintext::from_str("19field").unwrap());
        let r3 = Value::Plaintext(Plaintext::from_str("11field").unwrap());
        let r4 = Value::Plaintext(Plaintext::from_str("8field").unwrap());

        {
            // Construct the process.
            let process = crate::process::test_helpers::sample_process(&program);
            // Check that the circuit key can be synthesized.
            process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, &mut TestRng::default()).unwrap();
        }

        // Construct the process.
        let process = crate::process::test_helpers::sample_process(&program);

        // Compute the authorization.
        let authorization = {
            // Initialize an RNG.
            let rng = &mut TestRng::default();

            // Initialize caller private key.
            let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

            // Authorize the function call.
            let authorization = process
                .authorize::<CurrentAleo, _>(
                    &caller_private_key,
                    program.id(),
                    function_name,
                    [r0.clone(), r1.clone()].iter(),
                    rng,
                )
                .unwrap();
            assert_eq!(authorization.len(), 1);
            authorization
        };

        // Retrieve the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Compute the output value.
        let response =
            stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization.replicate()).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(3, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);

        // Re-run to ensure state continues to work.
        let response = stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(3, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);

        use circuit::Environment;

        // Ensure the environment is clean.
        assert_eq!(0, CurrentAleo::num_constants());
        assert_eq!(1, CurrentAleo::num_public());
        assert_eq!(0, CurrentAleo::num_private());
        assert_eq!(0, CurrentAleo::num_constraints());

        // Initialize an RNG.
        let rng = &mut TestRng::default();
        // Initialize a burner private key.
        let burner_private_key = PrivateKey::new(rng).unwrap();
        // Authorize the function call, with a burner private key.
        let authorization = process
            .authorize::<CurrentAleo, _>(&burner_private_key, program.id(), function_name, [r0, r1].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);

        // Re-run to ensure state continues to work.
        let execution = Arc::new(RwLock::new(Execution::new()));
        let inclusion = Arc::new(RwLock::new(Inclusion::new()));
        let metrics = Arc::new(RwLock::new(Vec::new()));
        let call_stack = CallStack::execute(authorization, execution, inclusion, metrics).unwrap();
        let response = stack.execute_function::<CurrentAleo, _>(call_stack, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(3, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);
    }

    #[test]
    fn test_program_evaluate_cast() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token_with_cast.aleo;

record token:
    owner as address.private;
    token_amount as u64.private;

function compute:
    input r0 as token.record;
    cast r0.owner r0.token_amount into r1 as token.record;
    output r1 as token.record;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();

        // Initialize an RNG.
        let rng = &mut TestRng::default();

        // Initialize caller private key.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the input value.
        let input_record = Record::from_str(&format!(
            "{{ owner: {caller}.private, token_amount: 100u64.private, _nonce: 0group.public }}"
        ))
        .unwrap();
        let input = Value::<CurrentNetwork>::Record(input_record);

        // Construct the process.
        let process = crate::process::test_helpers::sample_process(&program);

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [input].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.peek_next().unwrap();

        // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
        let randomizer = CurrentNetwork::hash_to_scalar_psd2(&[*request.tvk(), Field::from_u64(1)]).unwrap();
        let nonce = CurrentNetwork::g_scalar_multiply(&randomizer);

        // Declare the expected output value.
        let expected = Value::from_str(&format!(
            "{{ owner: {caller}.private, token_amount: 100u64.private, _nonce: {nonce}.public }}"
        ))
        .unwrap();

        // Retrieve the stack.
        let stack = process.get_stack(program.id()).unwrap();

        // Compute the output value.
        let response =
            stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization.replicate()).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let response = stack.evaluate_function::<CurrentAleo>(CallStack::evaluate(authorization).unwrap()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }
}
