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

mod closure;
pub use closure::*;

mod function;
pub use function::*;

mod instruction;
pub use instruction::*;

mod register_types;
pub use register_types::*;

mod stack;
pub use stack::*;

mod matches;
mod parse;

use console::{
    network::prelude::*,
    program::{
        EntryType,
        Identifier,
        Interface,
        Plaintext,
        PlaintextType,
        Record,
        RecordType,
        Register,
        RegisterType,
        Value,
        ValueType,
    },
};

use indexmap::IndexMap;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum ProgramDefinition {
    /// A program interface.
    Interface,
    /// A program record.
    Record,
    /// A program closure.
    Closure,
    /// A program function.
    Function,
}

#[derive(Clone, PartialEq, Eq)]
pub struct Program<N: Network> {
    /// The name of the program.
    name: Identifier<N>,
    /// A map of identifiers to their program declaration.
    identifiers: IndexMap<Identifier<N>, ProgramDefinition>,
    /// A map of the declared interfaces for the program.
    interfaces: IndexMap<Identifier<N>, Interface<N>>,
    /// A map of the declared record types for the program.
    records: IndexMap<Identifier<N>, RecordType<N>>,
    /// A map of the declared closures for the program.
    closures: IndexMap<Identifier<N>, Closure<N>>,
    /// A map of the declared register types for each closure.
    closure_registers: IndexMap<Identifier<N>, RegisterTypes<N>>,
    /// A map of the declared functions for the program.
    functions: IndexMap<Identifier<N>, Function<N>>,
    /// A map of the declared register types for each function.
    function_registers: IndexMap<Identifier<N>, RegisterTypes<N>>,
}

impl<N: Network> Program<N> {
    /// Initializes an empty program.
    #[inline]
    pub fn new(name: Identifier<N>) -> Self {
        Self {
            name,
            identifiers: IndexMap::new(),
            interfaces: IndexMap::new(),
            records: IndexMap::new(),
            closures: IndexMap::new(),
            closure_registers: IndexMap::new(),
            functions: IndexMap::new(),
            function_registers: IndexMap::new(),
        }
    }

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate(
        &self,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
    ) -> Result<Vec<Value<N, Plaintext<N>>>> {
        // Evaluate the function.
        Stack::evaluate(self.clone(), function_name, inputs)
    }

    /// Executes a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute(
        &self,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
    ) -> Result<Vec<Value<N, Plaintext<N>>>> {
        // Execute the function.
        Stack::execute(self.clone(), function_name, inputs)
    }

    /// Returns `true` if the program contains a interface with the given name.
    pub fn contains_interface(&self, name: &Identifier<N>) -> bool {
        self.interfaces.contains_key(name)
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

    /// Returns the interface with the given name.
    pub fn get_interface(&self, name: &Identifier<N>) -> Result<Interface<N>> {
        self.interfaces.get(name).cloned().ok_or_else(|| anyhow!("Interface '{name}' is not defined."))
    }

    /// Returns the record with the given name.
    pub fn get_record(&self, name: &Identifier<N>) -> Result<RecordType<N>> {
        self.records.get(name).cloned().ok_or_else(|| anyhow!("Record '{name}' is not defined."))
    }

    /// Returns the closure with the given name.
    pub fn get_closure(&self, name: &Identifier<N>) -> Result<Closure<N>> {
        self.closures.get(name).cloned().ok_or_else(|| anyhow!("Closure '{name}' is not defined."))
    }

    /// Returns the closure registers with the given name.
    pub fn get_closure_registers(&self, name: &Identifier<N>) -> Result<RegisterTypes<N>> {
        self.closure_registers.get(name).cloned().ok_or_else(|| anyhow!("Closure '{name}' is missing registers."))
    }

    /// Returns the function with the given name.
    pub fn get_function(&self, name: &Identifier<N>) -> Result<Function<N>> {
        self.functions.get(name).cloned().ok_or_else(|| anyhow!("Function '{name}' is not defined."))
    }

    /// Returns the function registers with the given name.
    pub fn get_function_registers(&self, name: &Identifier<N>) -> Result<RegisterTypes<N>> {
        self.function_registers.get(name).cloned().ok_or_else(|| anyhow!("Function '{name}' is missing registers."))
    }
}

impl<N: Network> Program<N> {
    /// Adds a new interface to the program.
    ///
    /// # Errors
    /// This method will halt if the interface was previously added.
    /// This method will halt if the interface name is already in use in the program.
    /// This method will halt if the interface name is a reserved opcode or keyword.
    /// This method will halt if any interfaces in the interface's members are not already defined.
    #[inline]
    fn add_interface(&mut self, interface: Interface<N>) -> Result<()> {
        // Retrieve the interface name.
        let interface_name = interface.name().clone();

        // Ensure the interface name is new.
        ensure!(self.is_unique_name(&interface_name), "'{interface_name}' is already in use.");
        // Ensure the interface name is not a reserved opcode.
        ensure!(!self.is_reserved_opcode(&interface_name), "'{interface_name}' is a reserved opcode.");
        // Ensure the interface name is not a reserved keyword.
        ensure!(!self.is_reserved_keyword(&interface_name), "'{interface_name}' is a reserved keyword.");

        // Ensure all interface members are well-formed.
        // Note: This design ensures cyclic references are not possible.
        for (identifier, plaintext_type) in interface.members() {
            // Ensure the member name is not a reserved keyword.
            ensure!(!self.is_reserved_keyword(identifier), "'{identifier}' is a reserved keyword.");
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
    /// This method will halt if the record name is a reserved opcode or keyword.
    /// This method will halt if any records in the record's members are not already defined.
    #[inline]
    fn add_record(&mut self, record: RecordType<N>) -> Result<()> {
        // For now, ensure only one record type exists in the program.
        ensure!(self.records.len() <= 1, "Only one record type is allowed in the program (for now).");

        // Retrieve the record name.
        let record_name = record.name().clone();

        // Ensure the record name is new.
        ensure!(self.is_unique_name(&record_name), "'{record_name}' is already in use.");
        // Ensure the record name is not a reserved opcode.
        ensure!(!self.is_reserved_opcode(&record_name), "'{record_name}' is a reserved opcode.");
        // Ensure the record name is not a reserved keyword.
        ensure!(!self.is_reserved_keyword(&record_name), "'{record_name}' is a reserved keyword.");

        // Ensure all record entries are well-formed.
        // Note: This design ensures cyclic references are not possible.
        for (identifier, entry_type) in record.entries() {
            // Ensure the member name is not a reserved keyword.
            ensure!(!self.is_reserved_keyword(identifier), "'{identifier}' is a reserved keyword.");
            // Ensure the member type is already defined in the program.
            match entry_type {
                // Ensure the plaintext type is already defined.
                EntryType::Constant(plaintext_type)
                | EntryType::Public(plaintext_type)
                | EntryType::Private(plaintext_type) => match plaintext_type {
                    PlaintextType::Literal(..) => continue,
                    PlaintextType::Interface(identifier) => {
                        if !self.interfaces.contains_key(identifier) {
                            bail!("Interface '{identifier}' in record '{record_name}' is not defined.")
                        }
                    }
                },
            }
        }

        // Add the record name to the identifiers.
        if self.identifiers.insert(record_name.clone(), ProgramDefinition::Record).is_some() {
            bail!("'{record_name}' already exists in the program.")
        }
        // Add the record to the program.
        if self.records.insert(record_name.clone(), record).is_some() {
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
        let closure_name = closure.name().clone();

        // Ensure the closure name is new.
        ensure!(self.is_unique_name(&closure_name), "'{closure_name}' is already in use.");
        // Ensure the closure name is not a reserved opcode.
        ensure!(!self.is_reserved_opcode(&closure_name), "'{closure_name}' is a reserved opcode.");
        // Ensure the closure name is not a reserved keyword.
        ensure!(!self.is_reserved_keyword(&closure_name), "'{closure_name}' is a reserved keyword.");

        // Initialize a map of registers to their types.
        let mut register_types = RegisterTypes::new();

        // Step 1. Check the function inputs are well-formed.
        for input in closure.inputs() {
            match input.register_type() {
                RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
                RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                    // Ensure the interface is defined in the program.
                    if !self.interfaces.contains_key(interface_name) {
                        bail!("Interface '{interface_name}' in closure '{closure_name}' is not defined.")
                    }
                }
                RegisterType::Record(identifier) => {
                    // Ensure the record type is defined in the program.
                    if !self.records.contains_key(identifier) {
                        bail!("Record '{identifier}' in closure '{closure_name}' is not defined.")
                    }
                }
            };

            // Insert the input register.
            register_types.add_input(input.register().clone(), *input.register_type())?;
        }

        // Step 2. Check the closure instructions are well-formed.
        for instruction in closure.instructions() {
            // Ensure the opcode is defined.
            match instruction.opcode() {
                Opcode::Literal(opcode) => {
                    // Ensure the opcode **is** a reserved opcode.
                    ensure!(self.is_reserved_opcode(&Identifier::from_str(opcode)?), "'{opcode}' is not an opcode.");
                    // Ensure the instruction is not the cast operation.
                    ensure!(!matches!(instruction, Instruction::Cast(..)), "Instruction '{instruction}' is a 'cast'.");
                    // Ensure the instruction has one destination register.
                    ensure!(
                        instruction.destinations().len() == 1,
                        "Instruction '{instruction}' has multiple destinations."
                    );
                }
                Opcode::Call => {
                    // Retrieve the call operation.
                    let operation = match instruction {
                        Instruction::Call(operation) => operation,
                        _ => bail!("Instruction '{instruction}' is not a call operation."),
                    };

                    // Retrieve the closure name.
                    let closure_name = operation.name();
                    // Ensure the operation is defined.
                    if !self.closures.contains_key(closure_name) {
                        bail!("Closure '{closure_name}' is not defined.")
                    }
                }
                Opcode::Cast => {
                    // Retrieve the cast operation.
                    let operation = match instruction {
                        Instruction::Cast(operation) => operation,
                        _ => bail!("Instruction '{instruction}' is not a cast operation."),
                    };

                    // Ensure the instruction has one destination register.
                    ensure!(
                        instruction.destinations().len() == 1,
                        "Instruction '{instruction}' has multiple destinations."
                    );

                    // Ensure the casted register type is defined.
                    match operation.register_type() {
                        RegisterType::Plaintext(PlaintextType::Literal(..)) => {
                            bail!("Casting to literal is currently unsupported")
                        }
                        RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                            // Ensure the interface name exists in the program.
                            if !self.interfaces.contains_key(interface_name) {
                                bail!("Interface '{interface_name}' in closure '{closure_name}' is not defined.")
                            }
                            // Retrieve the interface.
                            let interface = self.get_interface(&interface_name)?;
                            // Ensure the operand types match the interface.
                            register_types.matches_interface(&self, instruction.operands(), &interface)?;
                        }
                        RegisterType::Record(record_name) => {
                            // Ensure the record type is defined in the program.
                            if !self.records.contains_key(record_name) {
                                bail!("Record '{record_name}' in closure '{closure_name}' is not defined.")
                            }
                            // Retrieve the record type.
                            let record_type = self.get_record(&record_name)?;
                            // Ensure the operand types match the record type.
                            register_types.matches_record(&self, instruction.operands(), &record_type)?;
                        }
                    }
                }
            }

            // Initialize a vector to store the register types of the operands.
            let mut operand_types = Vec::with_capacity(instruction.operands().len());
            // Iterate over the operands, and retrieve the register type of each operand.
            for operand in instruction.operands() {
                // Retrieve and append the register type.
                operand_types.push(match operand {
                    Operand::Literal(literal) => RegisterType::Plaintext(PlaintextType::from(literal.to_type())),
                    Operand::Register(register) => register_types.get_type(&self, &register)?,
                });
            }

            // Compute the destination register types.
            let destination_types = instruction.output_types(&self, &operand_types)?;

            // Insert the destination register.
            for (destination, destination_type) in
                instruction.destinations().iter().zip_eq(destination_types.into_iter())
            {
                // Ensure the destination register is a locator (and does not reference a member).
                ensure!(matches!(destination, Register::Locator(..)), "Destination '{destination}' must be a locator.");
                // Insert the destination register.
                register_types.add_destination(destination.clone(), destination_type)?;
            }
        }

        // Step 3. Check the function outputs are well-formed.
        for output in closure.outputs() {
            // Retrieve the output register.
            let register = output.register();
            // Inform the user the output register is an input register, to ensure this is intended behavior.
            if register_types.is_input(register) {
                eprintln!("Output {register} in '{closure_name}' is an input register, ensure this is intended");
            }

            match output.register_type() {
                RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
                RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                    // Ensure the interface is defined in the program.
                    if !self.interfaces.contains_key(interface_name) {
                        bail!("Interface '{interface_name}' in closure '{closure_name}' is not defined.")
                    }
                }
                RegisterType::Record(identifier) => {
                    // Ensure the record type is defined in the program.
                    if !self.records.contains_key(identifier) {
                        bail!("Record '{identifier}' in closure '{closure_name}' is not defined.")
                    }
                }
            };

            // Retrieve the register type (as a plaintext type).
            // Note: This serves as the expected output type, which we will compare against.
            let register_type = register_types.get_type(&self, &register)?;

            // Ensure the register type and the output type match.
            if register_type != *output.register_type() {
                bail!("Output '{register}' does not match the expected output register type.")
            }

            // Insert the output register.
            register_types.add_output(output.register(), *output.register_type())?;
        }

        // Add the function name to the identifiers.
        if self.identifiers.insert(closure_name.clone(), ProgramDefinition::Closure).is_some() {
            bail!("'{closure_name}' already exists in the program.")
        }
        // Add the closure to the program.
        if self.closures.insert(closure_name.clone(), closure).is_some() {
            bail!("'{closure_name}' already exists in the program.")
        }
        // Add the closure registers to the program.
        if self.closure_registers.insert(closure_name.clone(), register_types).is_some() {
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
        let function_name = function.name().clone();

        // Ensure the function name is new.
        ensure!(self.is_unique_name(&function_name), "'{function_name}' is already in use.");
        // Ensure the function name is not a reserved opcode.
        ensure!(!self.is_reserved_opcode(&function_name), "'{function_name}' is a reserved opcode.");
        // Ensure the function name is not a reserved keyword.
        ensure!(!self.is_reserved_keyword(&function_name), "'{function_name}' is a reserved keyword.");

        // Initialize a map of registers to their types.
        let mut register_types = RegisterTypes::new();

        // Step 1. Check the function inputs are well-formed.
        for input in function.inputs() {
            // Retrieve the register type.
            let register_type = match input.value_type() {
                ValueType::Constant(plaintext_type)
                | ValueType::Public(plaintext_type)
                | ValueType::Private(plaintext_type) => {
                    // Ensure the plaintext type is defined in the program.
                    match plaintext_type {
                        PlaintextType::Literal(..) => (),
                        PlaintextType::Interface(interface_name) => {
                            // Ensure the interface name exists in the program.
                            if !self.interfaces.contains_key(interface_name) {
                                bail!("Interface '{interface_name}' in function '{function_name}' is not defined.")
                            }
                        }
                    }
                    // Output the register type.
                    RegisterType::Plaintext(plaintext_type.clone())
                }
                ValueType::Record(identifier) => {
                    // Ensure the record type is defined in the program.
                    if !self.records.contains_key(identifier) {
                        bail!("Record '{identifier}' in function '{function_name}' is not defined.")
                    }
                    // Output the register type.
                    RegisterType::Record(identifier.clone())
                }
            };

            // Insert the input register.
            register_types.add_input(input.register().clone(), register_type)?;
        }

        // Step 2. Check the function instructions are well-formed.
        for instruction in function.instructions() {
            // Ensure the opcode is defined.
            match instruction.opcode() {
                Opcode::Literal(opcode) => {
                    // Ensure the opcode **is** a reserved opcode.
                    ensure!(self.is_reserved_opcode(&Identifier::from_str(opcode)?), "'{opcode}' is not an opcode.");
                    // Ensure the instruction is not the cast operation.
                    ensure!(!matches!(instruction, Instruction::Cast(..)), "Instruction '{instruction}' is a 'cast'.");
                    // Ensure the instruction has one destination register.
                    ensure!(
                        instruction.destinations().len() == 1,
                        "Instruction '{instruction}' has multiple destinations."
                    );
                }
                Opcode::Call => {
                    // Retrieve the call operation.
                    let operation = match instruction {
                        Instruction::Call(operation) => operation,
                        _ => bail!("Instruction '{instruction}' is not a call operation."),
                    };

                    // Retrieve the closure name.
                    let closure_name = operation.name();
                    // Ensure the operation is defined.
                    if !self.closures.contains_key(closure_name) {
                        bail!("Closure '{closure_name}' is not defined.")
                    }
                }
                Opcode::Cast => {
                    // Retrieve the cast operation.
                    let operation = match instruction {
                        Instruction::Cast(operation) => operation,
                        _ => bail!("Instruction '{instruction}' is not a cast operation."),
                    };

                    // Ensure the instruction has one destination register.
                    ensure!(
                        instruction.destinations().len() == 1,
                        "Instruction '{instruction}' has multiple destinations."
                    );

                    // Ensure the casted register type is defined.
                    match operation.register_type() {
                        RegisterType::Plaintext(PlaintextType::Literal(..)) => {
                            bail!("Casting to literal is currently unsupported")
                        }
                        RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                            // Ensure the interface name exists in the program.
                            if !self.interfaces.contains_key(interface_name) {
                                bail!("Interface '{interface_name}' in function '{function_name}' is not defined.")
                            }
                            // Retrieve the interface.
                            let interface = self.get_interface(&interface_name)?;
                            // Ensure the operand types match the interface.
                            register_types.matches_interface(&self, instruction.operands(), &interface)?;
                        }
                        RegisterType::Record(record_name) => {
                            // Ensure the record type is defined in the program.
                            if !self.records.contains_key(record_name) {
                                bail!("Record '{record_name}' in function '{function_name}' is not defined.")
                            }
                            // Retrieve the record type.
                            let record_type = self.get_record(&record_name)?;
                            // Ensure the operand types match the record type.
                            register_types.matches_record(&self, instruction.operands(), &record_type)?;
                        }
                    }
                }
            }

            // Initialize a vector to store the register types of the operands.
            let mut operand_types = Vec::with_capacity(instruction.operands().len());
            // Iterate over the operands, and retrieve the register type of each operand.
            for operand in instruction.operands() {
                // Retrieve and append the register type.
                operand_types.push(match operand {
                    Operand::Literal(literal) => RegisterType::Plaintext(PlaintextType::from(literal.to_type())),
                    Operand::Register(register) => register_types.get_type(&self, &register)?,
                });
            }

            // Compute the destination register types.
            let destination_types = instruction.output_types(&self, &operand_types)?;

            // Insert the destination register.
            for (destination, destination_type) in
                instruction.destinations().iter().zip_eq(destination_types.into_iter())
            {
                // Ensure the destination register is a locator (and does not reference a member).
                ensure!(matches!(destination, Register::Locator(..)), "Destination '{destination}' must be a locator.");
                // Insert the destination register.
                register_types.add_destination(destination.clone(), destination_type)?;
            }
        }

        // Step 3. Check the function outputs are well-formed.
        for output in function.outputs() {
            // Retrieve the output register.
            let register = output.register();
            // Inform the user the output register is an input register, to ensure this is intended behavior.
            if register_types.is_input(register) {
                eprintln!("Output {register} in '{function_name}' is an input register, ensure this is intended");
            }

            // Retrieve the register type (as a plaintext type).
            // Note: This serves as the expected output type, which we will compare against.
            let register_type = register_types.get_type(&self, &register)?;

            match output.value_type() {
                ValueType::Constant(plaintext_type)
                | ValueType::Public(plaintext_type)
                | ValueType::Private(plaintext_type) => {
                    // Ensure the plaintext type is defined in the program.
                    match plaintext_type {
                        PlaintextType::Literal(..) => (),
                        PlaintextType::Interface(interface_name) => {
                            // Ensure the interface name exists in the program.
                            if !self.interfaces.contains_key(interface_name) {
                                bail!("Interface '{interface_name}' in function '{function_name}' is not defined.")
                            }
                        }
                    }
                    // Ensure the register type matches the output type.
                    ensure!(
                        register_type == RegisterType::Plaintext(plaintext_type.clone()),
                        "Output '{register}' in '{function_name}' has type '{register_type}', but expected type '{plaintext_type}'."
                    );
                }
                ValueType::Record(identifier) => {
                    // Ensure the record type is defined in the program.
                    if !self.records.contains_key(identifier) {
                        bail!("Record '{identifier}' in function '{function_name}' is not defined.")
                    }
                    // Ensure the register type matches the output type.
                    ensure!(
                        register_type == RegisterType::Record(identifier.clone()),
                        "Output '{register}' in '{function_name}' has type '{register_type}', but expected type '{identifier}'."
                    );
                }
            };

            // Insert the output register.
            register_types.add_output(output.register(), register_type)?;
        }

        // Add the function name to the identifiers.
        if self.identifiers.insert(function_name.clone(), ProgramDefinition::Function).is_some() {
            bail!("'{function_name}' already exists in the program.")
        }
        // Add the function to the program.
        if self.functions.insert(function_name.clone(), function).is_some() {
            bail!("'{function_name}' already exists in the program.")
        }
        // Add the function registers to the program.
        if self.function_registers.insert(function_name.clone(), register_types).is_some() {
            bail!("'{function_name}' already exists in the program.")
        }
        Ok(())
    }

    /// Returns `true` if the given name does not already exist in the program.
    fn is_unique_name(&self, name: &Identifier<N>) -> bool {
        !self.identifiers.contains_key(name)
    }

    /// Returns `true` if the given name is a reserved opcode.
    fn is_reserved_opcode(&self, name: &Identifier<N>) -> bool {
        // Convert the name to a string.
        let name = name.to_string();
        // Check if it matches root of any opcode.
        Instruction::<N>::OPCODES.into_iter().any(|opcode| (**opcode).splitn(2, '.').next() == Some(&name))
    }

    /// Returns `true` if the given name uses a reserved keyword.
    fn is_reserved_keyword(&self, name: &Identifier<N>) -> bool {
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
            // Program
            "function",
            "interface",
            "record",
            "closure",
            "program",
            "global",
            // Reserved (catch all)
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
        // Convert the given name to a string.
        let name = name.to_string();
        // Check if the name is a keyword.
        KEYWORDS.iter().any(|keyword| *keyword == &name)
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
    use console::network::Testnet3;

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
        let mut program = Program::<CurrentNetwork>::new(Identifier::from_str("unknown")?);

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
    owner as address.private;
    balance as u64.private;
    first as field.private;
    second as field.public;",
        )?;

        // Initialize a new program.
        let mut program = Program::<CurrentNetwork>::new(Identifier::from_str("unknown")?);

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
        let mut program = Program::<CurrentNetwork>::new(Identifier::from_str("unknown")?);

        // Add the function to the program.
        program.add_function(function.clone())?;
        // Ensure the function was added.
        assert!(program.contains_function(&Identifier::from_str("compute")?));
        // Ensure the retrieved function matches.
        assert_eq!(function, program.get_function(&Identifier::from_str("compute")?)?);

        Ok(())
    }

    #[test]
    fn test_program_evaluate_function() {
        let program = Program::<CurrentNetwork>::from_str(
            r"
    program example;

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
        let inputs = vec![
            StackValue::<CurrentNetwork>::Plaintext(Plaintext::from_str("2field").unwrap()),
            StackValue::Plaintext(Plaintext::from_str("3field").unwrap()),
        ];

        // Run the function.
        let expected = Value::Private(Plaintext::<CurrentNetwork>::from_str("5field").unwrap());
        let candidate = program.evaluate(&function_name, &inputs).unwrap();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let candidate = program.evaluate(&function_name, &inputs).unwrap();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }

    #[test]
    fn test_program_evaluate_interface_and_function() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program example;

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

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();
        // Declare the input value.
        let input =
            StackValue::<CurrentNetwork>::Plaintext(Plaintext::from_str("{ first: 2field, second: 3field }").unwrap());
        // Declare the expected output value.
        let expected = Value::Private(Plaintext::from_str("5field").unwrap());

        // Compute the output value.
        let candidate = program.evaluate(&function_name, &[input.clone()]).unwrap();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let candidate = program.evaluate(&function_name, &[input]).unwrap();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }

    #[test]
    fn test_program_evaluate_record_and_function() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token;

record token:
    owner as address.private;
    balance as u64.private;
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
        // Declare the input value.
        let input =
            StackValue::<CurrentNetwork>::Record(Record::from_str("{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, balance: 5u64.private, token_amount: 100u64.private }").unwrap());
        // Declare the expected output value.
        let expected = Value::Private(Plaintext::from_str("200u64").unwrap());

        // Compute the output value.
        let candidate = program.evaluate(&function_name, &[input.clone()]).unwrap();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let candidate = program.evaluate(&function_name, &[input]).unwrap();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }

    #[test]
    fn test_program_evaluate_call() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program example_call;

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
        let r0 = StackValue::<CurrentNetwork>::Plaintext(Plaintext::from_str("3field").unwrap());
        let r1 = StackValue::<CurrentNetwork>::Plaintext(Plaintext::from_str("5field").unwrap());

        // Declare the expected output value.
        let r2 = Value::Private(Plaintext::from_str("19field").unwrap());
        let r3 = Value::Private(Plaintext::from_str("11field").unwrap());
        let r4 = Value::Private(Plaintext::from_str("8field").unwrap());

        // Compute the output value.
        let candidate = program.evaluate(&function_name, &[r0.clone(), r1.clone()]).unwrap();
        assert_eq!(3, candidate.len());
        assert_eq!(r2, candidate[0]);
        assert_eq!(r3, candidate[1]);
        assert_eq!(r4, candidate[2]);

        // Re-run to ensure state continues to work.
        let candidate = program.evaluate(&function_name, &[r0, r1]).unwrap();
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
program token_with_cast;

record token:
    owner as address.private;
    balance as u64.private;
    token_amount as u64.private;

function compute:
    input r0 as token.record;
    cast r0.owner r0.balance r0.token_amount into r1 as token.record;
    output r1 as token.record;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();
        // Declare the input value.
        let input_record = Record::from_str("{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, balance: 5u64.private, token_amount: 100u64.private }").unwrap();
        let input = StackValue::<CurrentNetwork>::Record(input_record.clone());
        // Declare the expected output value.
        let expected = Value::Record(input_record);

        // Compute the output value.
        let candidate = program.evaluate(&function_name, &[input.clone()]).unwrap();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);

        // Re-run to ensure state continues to work.
        let candidate = program.evaluate(&function_name, &[input]).unwrap();
        assert_eq!(1, candidate.len());
        assert_eq!(expected, candidate[0]);
    }
}
