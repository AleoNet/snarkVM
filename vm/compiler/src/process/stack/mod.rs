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

mod register_types;
pub use register_types::*;

mod load;
mod store;

use crate::{CallOperator, Closure, Function, Instruction, Opcode, Operand, Program};
use console::{
    network::prelude::*,
    program::{
        Entry,
        EntryType,
        Identifier,
        Interface,
        Literal,
        LiteralType,
        Plaintext,
        PlaintextType,
        ProgramID,
        RecordType,
        Register,
        RegisterType,
        Value,
        ValueType,
    },
};

use indexmap::IndexMap;

pub struct Stack<N: Network, A: circuit::Aleo<Network = N>> {
    /// The program (record types, interfaces, functions).
    program: Program<N>,
    /// The mapping of imported programs as `(program ID, program)`.
    imports: IndexMap<ProgramID<N>, Program<N>>,
    /// The mapping of all registers to their defined types.
    register_types: RegisterTypes<N>,
    /// The mapping of assigned console registers to their values.
    console_registers: IndexMap<u64, Value<N>>,
    /// The mapping of assigned circuit registers to their values.
    circuit_registers: IndexMap<u64, circuit::Value<A>>,
    /// The boolean indicator if the stack is for a setup.
    is_setup: bool,
}

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Initializes a new stack, given the program and register types.
    #[inline]
    pub fn new(program: Program<N>, is_setup: bool) -> Result<Self> {
        // TODO (howardwu): Process every closure and function before returning.
        Ok(Self {
            program,
            imports: IndexMap::new(),
            register_types: RegisterTypes::new(),
            console_registers: IndexMap::new(),
            circuit_registers: IndexMap::new(),
            is_setup,
        })
    }

    /// Adds a new imported program to the stack.
    #[inline]
    pub fn import_program(&mut self, program: &Program<N>) -> Result<()> {
        // Retrieve the program ID.
        let program_id = program.id();
        // Ensure the program is not already added.
        ensure!(!self.imports.contains_key(program_id), "Program '{program_id}' already exists");
        // TODO (howardwu): Ensure the imported program is declared in the program imports.
        // TODO (howardwu): Ensure the imported program is not the main program.

        // Check the program closures to the stack.
        for closure in program.closures().values() {
            self.process_closure(program, closure, false)?;
        }
        // Add the program functions to the stack.
        for function in program.functions().values() {
            self.process_function(program, function, false)?;
        }
        // Add the program to the stack.
        self.imports.insert(*program_id, program.clone());

        // Return success.
        Ok(())
    }

    /// Returns if the stack is for a setup.
    #[inline]
    pub const fn is_setup(&self) -> bool {
        self.is_setup
    }

    /// Returns the program.
    #[inline]
    pub const fn program(&self) -> &Program<N> {
        &self.program
    }

    /// Returns `true` if the stack contains the program (including imported programs).
    #[inline]
    pub fn contains_program(&self, program_id: &ProgramID<N>) -> bool {
        self.program.id() == program_id || self.imports.contains_key(program_id)
    }

    /// Returns the program (including an imported program) for the given program ID.
    #[inline]
    pub fn get_program(&self, program_id: &ProgramID<N>) -> Result<&Program<N>> {
        match self.program.id() == program_id {
            true => Ok(&self.program),
            false => self.imports.get(program_id).ok_or_else(|| anyhow!("Program '{program_id}' does not exist.")),
        }
    }

    /// Evaluates a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_closure(&mut self, closure: &Closure<N>, inputs: &[Value<N>]) -> Result<Vec<Value<N>>> {
        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }

        // Initialize the stack.
        self.process_closure(&self.program.clone(), closure, true)?;
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            self.store(register, input.clone())
        })?;

        // Evaluate the instructions.
        closure.instructions().iter().try_for_each(|instruction| instruction.evaluate(self))?;

        // Load the outputs.
        let outputs = closure.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            self.load(&Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Executes a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute_closure(
        &mut self,
        closure: &Closure<N>,
        inputs: &[circuit::Value<A>],
    ) -> Result<Vec<circuit::Value<A>>> {
        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }

        // Retrieve the number of public variables in the circuit.
        let num_public = A::num_public();

        // Initialize the stack.
        self.process_closure(&self.program.clone(), closure, true)?;
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            use circuit::Eject;

            if !self.is_setup {
                // Assign the console input to the register.
                self.store(register, input.eject_value())?;
            }
            // Assign the circuit input to the register.
            self.store_circuit(register, input.clone())
        })?;

        // If the circuit is not for a setup, then evaluate the instructions.
        if !self.is_setup {
            closure.instructions().iter().try_for_each(|instruction| instruction.evaluate(self))?;
        }
        // Execute the instructions.
        closure.instructions().iter().try_for_each(|instruction| instruction.execute(self))?;

        // Ensure the number of public variables remains the same.
        ensure!(A::num_public() == num_public, "Forbidden operation: instructions injected public variables");

        // Load the outputs.
        let outputs = closure.outputs().iter().map(|output| {
            // Retrieve the circuit output from the register.
            self.load_circuit(&Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_function(&mut self, function: &Function<N>, inputs: &[Value<N>]) -> Result<Vec<Value<N>>> {
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
        }

        // Initialize the stack.
        self.process_function(&self.program.clone(), function, true)?;
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            self.store(register, input.clone())
        })?;

        // Evaluate the instructions.
        function.instructions().iter().try_for_each(|instruction| instruction.evaluate(self))?;

        // Load the outputs.
        let outputs = function.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            self.load(&Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Executes a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute_function(
        &mut self,
        function: &Function<N>,
        inputs: &[circuit::Value<A>],
    ) -> Result<Vec<circuit::Value<A>>> {
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
        }

        // Retrieve the number of public variables in the circuit.
        let num_public = A::num_public();

        // Initialize the stack.
        self.process_function(&self.program.clone(), function, true)?;
        self.console_registers.clear();
        self.circuit_registers.clear();

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            use circuit::Eject;

            if !self.is_setup {
                // Assign the console input to the register.
                self.store(register, input.eject_value())?;
            }
            // Assign the circuit input to the register.
            self.store_circuit(register, input.clone())
        })?;

        // If the circuit is not for a setup, then evaluate the instructions.
        if !self.is_setup {
            function.instructions().iter().try_for_each(|instruction| instruction.evaluate(self))?;
        }
        // Execute the instructions.
        function.instructions().iter().try_for_each(|instruction| instruction.execute(self))?;

        // Ensure the number of public variables remains the same.
        ensure!(A::num_public() == num_public, "Forbidden operation: instructions injected public variables");

        // Load the outputs.
        let outputs = function.outputs().iter().map(|output| {
            // Retrieve the circuit output from the register.
            self.load_circuit(&Operand::Register(output.register().clone()))
        });

        outputs.collect()
    }

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn test_evaluate(&mut self, function_name: &Identifier<N>, inputs: &[Value<N>]) -> Result<Vec<Value<N>>> {
        // Retrieve the function from the program.
        let function = self.program.get_function(function_name)?;
        // Evaluate the function.
        self.evaluate_function(&function, inputs)
    }

    /// Executes a program function on the given inputs.
    ///
    /// Note: To execute a transition, do **not** call this method. Instead, call `Process::execute`.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn test_execute(
        &mut self,
        function_name: &Identifier<N>,
        inputs: &[Value<N>],
    ) -> Result<Vec<circuit::Value<A>>> {
        // Ensure the circuit environment is clean.
        A::reset();

        // Retrieve the function from the program.
        let function = self.program.get_function(function_name)?;

        // Inject the inputs to the circuit environment.
        let inputs = function
            .inputs()
            .iter()
            .map(|i| i.value_type())
            .zip_eq(inputs)
            .map(|(value_type, input)| {
                // Inject the inputs according to their value type.
                match value_type {
                    ValueType::Constant(..) => circuit::Inject::new(circuit::Mode::Constant, input.clone()),
                    ValueType::Public(..) => circuit::Inject::new(circuit::Mode::Public, input.clone()),
                    ValueType::Private(..) => circuit::Inject::new(circuit::Mode::Private, input.clone()),
                    ValueType::Record(..) => circuit::Inject::new(circuit::Mode::Private, input.clone()),
                }
            })
            .collect::<Vec<_>>();

        // Execute the function.
        self.execute_function(&function, &inputs)
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Checks that the given closure is well-formed for the given program. If `is_main` is `true`,
    /// the register types will be set in the `Stack` for use as the main call.
    fn process_closure(&mut self, program: &Program<N>, closure: &Closure<N>, is_main: bool) -> Result<()> {
        // // Initialize a stack for the closure.
        // let mut stack = Stack::new();
        //
        // // Add the closure stack to the program.
        // if self.closure_stacks.insert(closure_name, stack).is_some() {
        //     bail!("'{closure_name}' already exists in the program.")
        // }

        // Initialize a map of registers to their types.
        let mut register_types = RegisterTypes::new();

        // Step 1. Check the inputs are well-formed.
        for input in closure.inputs() {
            // Check the input register type.
            Self::check_input(program, &mut register_types, input.register(), input.register_type())?;
        }

        // Step 2. Check the instructions are well-formed.
        for instruction in closure.instructions() {
            // Check the instruction opcode, operands, and destinations.
            self.check_instruction(program, &mut register_types, instruction)?;
        }

        // Step 3. Check the outputs are well-formed.
        for output in closure.outputs() {
            // Check the output register type.
            Self::check_output(program, &register_types, output.register(), output.register_type())?;
        }

        // If this is the main call, save the register types.
        if is_main {
            self.register_types = register_types;
        }

        Ok(())
    }

    /// Checks that the given function is well-formed for the given program. If `is_main` is `true`,
    /// the register types will be set in the `Stack` for use as the main call.
    fn process_function(&mut self, program: &Program<N>, function: &Function<N>, is_main: bool) -> Result<()> {
        // Initialize a map of registers to their types.
        let mut register_types = RegisterTypes::new();

        // Step 1. Check the inputs are well-formed.
        for input in function.inputs() {
            // Check the input register type.
            Self::check_input(program, &mut register_types, input.register(), &match input.value_type() {
                ValueType::Constant(plaintext_type)
                | ValueType::Public(plaintext_type)
                | ValueType::Private(plaintext_type) => RegisterType::Plaintext(*plaintext_type),
                ValueType::Record(identifier) => RegisterType::Record(*identifier),
            })?;
        }

        // Step 2. Check the instructions are well-formed.
        for instruction in function.instructions() {
            // Check the instruction opcode, operands, and destinations.
            self.check_instruction(program, &mut register_types, instruction)?;
        }

        // Step 3. Check the outputs are well-formed.
        for output in function.outputs() {
            // Retrieve the register type and check the output register type.
            Self::check_output(program, &register_types, output.register(), &match output.value_type() {
                ValueType::Constant(plaintext_type)
                | ValueType::Public(plaintext_type)
                | ValueType::Private(plaintext_type) => RegisterType::Plaintext(*plaintext_type),
                ValueType::Record(identifier) => RegisterType::Record(*identifier),
            })?;
        }

        // If this is the main call, save the register types.
        if is_main {
            self.register_types = register_types;
        }

        Ok(())
    }

    /// Ensure the given input register is well-formed.
    fn check_input(
        program: &Program<N>,
        register_types: &mut RegisterTypes<N>,
        register: &Register<N>,
        register_type: &RegisterType<N>,
    ) -> Result<()> {
        // Ensure the register type is defined in the program.
        match register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
            RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                // Ensure the interface is defined in the program.
                if !program.contains_interface(interface_name) {
                    bail!("Interface '{interface_name}' in '{}' is not defined.", program.id())
                }
            }
            RegisterType::Record(identifier) => {
                // Ensure the record type is defined in the program.
                if !program.contains_record(identifier) {
                    bail!("Record '{identifier}' in '{}' is not defined.", program.id())
                }
            }
        };

        // Insert the input register.
        register_types.add_input(register.clone(), *register_type)?;

        // Ensure the register type and the input type match.
        if *register_type != register_types.get_type(program, register)? {
            bail!("Input '{register}' does not match the expected input register type.")
        }
        Ok(())
    }

    /// Ensure the given output register is well-formed.
    fn check_output(
        program: &Program<N>,
        register_types: &RegisterTypes<N>,
        register: &Register<N>,
        register_type: &RegisterType<N>,
    ) -> Result<()> {
        // Inform the user the output register is an input register, to ensure this is intended behavior.
        if register_types.is_input(register) {
            eprintln!("Output {register} in '{}' is an input register, ensure this is intended", program.id());
        }

        // Ensure the register type is defined in the program.
        match register_type {
            RegisterType::Plaintext(PlaintextType::Literal(..)) => (),
            RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                // Ensure the interface is defined in the program.
                if !program.contains_interface(interface_name) {
                    bail!("Interface '{interface_name}' in '{}' is not defined.", program.id())
                }
            }
            RegisterType::Record(identifier) => {
                // Ensure the record type is defined in the program.
                if !program.contains_record(identifier) {
                    bail!("Record '{identifier}' in '{}' is not defined.", program.id())
                }
            }
        };

        // Ensure the register type and the output type match.
        if *register_type != register_types.get_type(program, register)? {
            bail!("Output '{register}' does not match the expected output register type.")
        }
        Ok(())
    }

    /// Ensures the given instruction is well-formed.
    fn check_instruction(
        &self,
        program: &Program<N>,
        register_types: &mut RegisterTypes<N>,
        instruction: &Instruction<N>,
    ) -> Result<()> {
        // Ensure the opcode is well-formed.
        self.check_instruction_opcode(program, register_types, instruction)?;

        // Initialize a vector to store the register types of the operands.
        let mut operand_types = Vec::with_capacity(instruction.operands().len());
        // Iterate over the operands, and retrieve the register type of each operand.
        for operand in instruction.operands() {
            // Retrieve and append the register type.
            operand_types.push(match operand {
                Operand::Literal(literal) => RegisterType::Plaintext(PlaintextType::from(literal.to_type())),
                Operand::Register(register) => register_types.get_type(program, register)?,
            });
        }

        // Compute the destination register types.
        let destination_types = instruction.output_types(self, &operand_types)?;

        // Insert the destination register.
        for (destination, destination_type) in
            instruction.destinations().into_iter().zip_eq(destination_types.into_iter())
        {
            // Ensure the destination register is a locator (and does not reference a member).
            ensure!(matches!(destination, Register::Locator(..)), "Destination '{destination}' must be a locator.");
            // Insert the destination register.
            register_types.add_destination(destination, destination_type)?;
        }
        Ok(())
    }

    /// Ensures the opcode is a valid opcode and corresponds to the correct instruction.
    /// This method is called when adding a new closure or function to the program.
    fn check_instruction_opcode(
        &self,
        program: &Program<N>,
        register_types: &RegisterTypes<N>,
        instruction: &Instruction<N>,
    ) -> Result<()> {
        match instruction.opcode() {
            Opcode::Literal(opcode) => {
                // Ensure the opcode **is** a reserved opcode.
                ensure!(Self::is_reserved_opcode(&Identifier::from_str(opcode)?), "'{opcode}' is not an opcode.");
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

                // Retrieve the operator.
                let operator = operation.operator();
                match operator {
                    CallOperator::Locator(locator) => {
                        // Retrieve the program ID.
                        let program_id = locator.program_id();
                        // Retrieve the resource from the locator.
                        let resource = match locator.resource() {
                            Some(resource) => resource,
                            // Ensure the locator contains a resource name.
                            None => bail!("Locator '{locator}' must reference a function or closure."),
                        };

                        // Retrieve the program.
                        let program = self.get_program(program_id)?;
                        // Ensure the function or closure exists in the program.
                        if !program.contains_function(resource) && !program.contains_closure(resource) {
                            bail!("'{resource}' is not defined in '{}'.", program.id())
                        }
                    }
                    CallOperator::Resource(resource) => {
                        // Ensure the function or closure exists in the program.
                        if !program.contains_function(resource) && !program.contains_closure(resource) {
                            bail!("'{resource}' is not defined in '{}'.", program.id())
                        }
                    }
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
                        if !program.contains_interface(interface_name) {
                            bail!("Interface '{interface_name}' is not defined.")
                        }
                        // Retrieve the interface.
                        let interface = program.get_interface(interface_name)?;
                        // Ensure the operand types match the interface.
                        register_types.matches_interface(program, instruction.operands(), &interface)?;
                    }
                    RegisterType::Record(record_name) => {
                        // Ensure the record type is defined in the program.
                        if !program.contains_record(record_name) {
                            bail!("Record '{record_name}' is not defined.")
                        }
                        // Retrieve the record type.
                        let record_type = program.get_record(record_name)?;
                        // Ensure the operand types match the record type.
                        register_types.matches_record(program, instruction.operands(), &record_type)?;
                    }
                }
            }
            Opcode::Commit(opcode) => {
                // Ensure the opcode **is** a reserved opcode.
                ensure!(Self::is_reserved_opcode(&Identifier::from_str(opcode)?), "'{opcode}' is not an opcode.");
                // Ensure the instruction belongs to the defined set.
                if ![
                    "commit.bhp256",
                    "commit.bhp512",
                    "commit.bhp768",
                    "commit.bhp1024",
                    "commit.ped64",
                    "commit.ped128",
                ]
                .contains(&opcode)
                {
                    bail!("Instruction '{instruction}' is not the opcode '{opcode}'.");
                }
                // Ensure the instruction is the correct one.
                // match opcode {
                //     "commit.bhp256" => ensure!(
                //         matches!(instruction, Instruction::CommitBHP256(..)),
                //         "Instruction '{instruction}' is not the opcode '{opcode}'."
                //     ),
                // }
            }
            Opcode::Hash(opcode) => {
                // Ensure the opcode **is** a reserved opcode.
                ensure!(Self::is_reserved_opcode(&Identifier::from_str(opcode)?), "'{opcode}' is not an opcode.");
                // Ensure the instruction belongs to the defined set.
                if ![
                    "hash.bhp256",
                    "hash.bhp512",
                    "hash.bhp768",
                    "hash.bhp1024",
                    "hash.ped64",
                    "hash.ped128",
                    "hash.psd2",
                    "hash.psd4",
                    "hash.psd8",
                ]
                .contains(&opcode)
                {
                    bail!("Instruction '{instruction}' is not the opcode '{opcode}'.");
                }
                // Ensure the instruction is the correct one.
                // match opcode {
                //     "hash.bhp256" => ensure!(
                //         matches!(instruction, Instruction::HashBHP256(..)),
                //         "Instruction '{instruction}' is not the opcode '{opcode}'."
                //     ),
                // }
            }
        }
        Ok(())
    }

    /// Returns `true` if the given name is a reserved opcode.
    fn is_reserved_opcode(name: &Identifier<N>) -> bool {
        // Convert the given name to a string.
        let name = name.to_string();
        // Check if the given name matches the root of any opcode (the first part, up to the first '.').
        Instruction::<N>::OPCODES.iter().any(|opcode| (**opcode).split('.').next() == Some(&name))
    }
}
