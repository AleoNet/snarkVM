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

use crate::{
    traits::{RegistersLoad, RegistersLoadCircuit, RegistersStore, RegistersStoreCircuit, StackMatches, StackProgram},
    Opcode,
    Operand,
};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType, Value},
    types::Boolean,
};

/// Computes whether `first` equals `second` as a boolean, storing the outcome in `destination`.
pub type IsEq<N> = IsInstruction<N, { Variant::IsEq as u8 }>;
/// Computes whether `first` does **not** equals `second` as a boolean, storing the outcome in `destination`.
pub type IsNeq<N> = IsInstruction<N, { Variant::IsNeq as u8 }>;

enum Variant {
    IsEq,
    IsNeq,
}

/// Computes an equality operation on two operands, and stores the outcome in `destination`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct IsInstruction<N: Network, const VARIANT: u8> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network, const VARIANT: u8> IsInstruction<N, VARIANT> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        match VARIANT {
            0 => Opcode::Is("is.eq"),
            1 => Opcode::Is("is.neq"),
            _ => panic!("Invalid 'is' instruction opcode"),
        }
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that the operands is exactly two inputs.
        debug_assert!(self.operands.len() == 2, "Instruction '{}' must have two operands", Self::opcode());
        // Return the operands.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }
}

impl<N: Network, const VARIANT: u8> IsInstruction<N, VARIANT> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the inputs.
        let input_a = registers.load(stack, &self.operands[0])?;
        let input_b = registers.load(stack, &self.operands[1])?;

        // Check the inputs.
        let output = match VARIANT {
            0 => Literal::Boolean(Boolean::new(input_a == input_b)),
            1 => Literal::Boolean(Boolean::new(input_a != input_b)),
            _ => bail!("Invalid 'is' variant: {VARIANT}"),
        };
        // Store the output.
        registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(output)))
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoadCircuit<N, A> + RegistersStoreCircuit<N, A>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the inputs.
        let input_a = registers.load_circuit(stack, &self.operands[0])?;
        let input_b = registers.load_circuit(stack, &self.operands[1])?;

        // Check the inputs.
        let output = match VARIANT {
            0 => circuit::Literal::Boolean(input_a.is_equal(&input_b)),
            1 => circuit::Literal::Boolean(input_a.is_not_equal(&input_b)),
            _ => bail!("Invalid 'is' variant: {VARIANT}"),
        };
        // Convert the output to a stack value.
        let output = circuit::Value::Plaintext(circuit::Plaintext::Literal(output, Default::default()));
        // Store the output.
        registers.store_circuit(stack, &self.destination, output)
    }

    /// Finalizes the instruction.
    #[inline]
    pub fn finalize(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        self.evaluate(stack, registers)
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(
        &self,
        _stack: &impl StackProgram<N>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 2 {
            bail!("Instruction '{}' expects 2 inputs, found {} inputs", Self::opcode(), input_types.len())
        }
        // Ensure the operands are of the same type.
        if input_types[0] != input_types[1] {
            bail!(
                "Instruction '{}' expects inputs of the same type. Found inputs of type '{}' and '{}'",
                Self::opcode(),
                input_types[0],
                input_types[1]
            )
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        match VARIANT {
            0 | 1 => Ok(vec![RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Boolean))]),
            _ => bail!("Invalid 'is' variant: {VARIANT}"),
        }
    }
}

impl<N: Network, const VARIANT: u8> Parser for IsInstruction<N, VARIANT> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the first operand from the string.
        let (string, first) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the second operand from the string.
        let (string, second) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        Ok((string, Self { operands: vec![first, second], destination }))
    }
}

impl<N: Network, const VARIANT: u8> FromStr for IsInstruction<N, VARIANT> {
    type Err = Error;

    /// Parses a string into an operation.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network, const VARIANT: u8> Debug for IsInstruction<N, VARIANT> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, const VARIANT: u8> Display for IsInstruction<N, VARIANT> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{operand} "))?;
        write!(f, "into {}", self.destination)
    }
}

impl<N: Network, const VARIANT: u8> FromBytes for IsInstruction<N, VARIANT> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(2);
        // Read the operands.
        for _ in 0..2 {
            operands.push(Operand::read_le(&mut reader)?);
        }
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self { operands, destination })
    }
}

impl<N: Network, const VARIANT: u8> ToBytes for IsInstruction<N, VARIANT> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(error(format!("The number of operands must be 2, found {}", self.operands.len())));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instruction::test_helpers::{sample_finalize_registers, sample_registers};
    use circuit::AleoV0;
    use console::{network::Testnet3, program::Identifier};
    use synthesizer::{
        process::Stack,
        snark::{ProvingKey, VerifyingKey},
    };

    use std::collections::HashMap;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    const ITERATIONS: usize = 100;

    /// Samples the stack. Note: Do not replicate this for real program use, it is insecure.
    #[allow(clippy::type_complexity)]
    fn sample_stack(
        opcode: Opcode,
        type_a: LiteralType,
        type_b: LiteralType,
        mode_a: circuit::Mode,
        mode_b: circuit::Mode,
        cache: &mut HashMap<String, (ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)>,
    ) -> Result<(Stack<CurrentNetwork>, Vec<Operand<CurrentNetwork>>, Register<CurrentNetwork>)> {
        use crate::Program;
        use synthesizer::Process;

        // Initialize the opcode.
        let opcode = opcode.to_string();

        // Initialize the function name.
        let function_name = Identifier::<CurrentNetwork>::from_str("run")?;

        // Initialize the registers.
        let r0 = Register::Locator(0);
        let r1 = Register::Locator(1);
        let r2 = Register::Locator(2);

        // Initialize the program.
        let program = Program::from_str(&format!(
            "program testing.aleo;
            function {function_name}:
                input {r0} as {type_a}.{mode_a};
                input {r1} as {type_b}.{mode_b};
                {opcode} {r0} {r1} into {r2};
                finalize {r0} {r1};

            finalize {function_name}:
                input {r0} as {type_a}.public;
                input {r1} as {type_b}.public;
                {opcode} {r0} {r1} into {r2};
        "
        ))?;

        // Initialize the operands.
        let operand_a = Operand::Register(r0);
        let operand_b = Operand::Register(r1);
        let operands = vec![operand_a, operand_b];

        // Initialize the stack.
        let stack = Stack::new(&Process::load_with_cache(cache)?, &program)?;

        Ok((stack, operands, r2))
    }

    fn check_is<const VARIANT: u8>(
        operation: impl FnOnce(
            Vec<Operand<CurrentNetwork>>,
            Register<CurrentNetwork>,
        ) -> IsInstruction<CurrentNetwork, VARIANT>,
        opcode: Opcode,
        literal_a: &Literal<CurrentNetwork>,
        literal_b: &Literal<CurrentNetwork>,
        mode_a: &circuit::Mode,
        mode_b: &circuit::Mode,
        cache: &mut HashMap<String, (ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)>,
    ) {
        use circuit::Eject;

        println!("Checking '{opcode}' for '{literal_a}.{mode_a}' and '{literal_b}.{mode_b}'");

        // Initialize the types.
        let type_a = literal_a.to_type();
        let type_b = literal_b.to_type();
        assert_eq!(type_a, type_b, "The two literals must be the *same* type for this test");

        // Initialize the stack.
        let (stack, operands, destination) = sample_stack(opcode, type_a, type_b, *mode_a, *mode_b, cache).unwrap();
        // Initialize the operation.
        let operation = operation(operands, destination.clone());
        // Initialize the function name.
        let function_name = Identifier::from_str("run").unwrap();
        // Initialize a destination operand.
        let destination_operand = Operand::Register(destination);

        /* First, check the operation *succeeds* when both operands are `literal_a.mode_a`. */
        {
            // Attempt to compute the valid operand case.
            let values = [(literal_a, None), (literal_a, None)];
            let mut registers = sample_registers(&stack, &function_name, &values).unwrap();
            operation.evaluate(&stack, &mut registers).unwrap();

            // Retrieve the output.
            let output_a = registers.load_literal(&stack, &destination_operand).unwrap();

            // Ensure the output is correct.
            if let Literal::Boolean(output_a) = output_a {
                match VARIANT {
                    0 => assert!(*output_a, "Instruction '{operation}' failed (console): {literal_a} {literal_a}"),
                    1 => assert!(
                        !*output_a,
                        "Instruction '{operation}' should have failed (console): {literal_a} {literal_a}"
                    ),
                    _ => panic!("Found an invalid 'is' variant in the test"),
                }
            } else {
                panic!("The output must be a boolean (console)");
            }

            // Attempt to compute the valid operand case.
            let values = [(literal_a, Some(*mode_a)), (literal_a, Some(*mode_a))];
            let mut registers = sample_registers(&stack, &function_name, &values).unwrap();
            operation.execute::<CurrentAleo>(&stack, &mut registers).unwrap();

            // Retrieve the output.
            let output_b = registers.load_literal_circuit(&stack, &destination_operand).unwrap();

            // Ensure the output is correct.
            if let circuit::Literal::Boolean(output_b) = output_b {
                match VARIANT {
                    0 => assert!(
                        output_b.eject_value(),
                        "Instruction '{operation}' failed (circuit): {literal_a}.{mode_a} {literal_a}.{mode_a}"
                    ),
                    1 => assert!(
                        !output_b.eject_value(),
                        "Instruction '{operation}' should have failed (circuit): {literal_a}.{mode_a} {literal_a}.{mode_a}"
                    ),
                    _ => panic!("Found an invalid 'is' variant in the test"),
                }
            } else {
                panic!("The output must be a boolean (circuit)");
            }

            // Ensure the circuit is satisfied.
            match VARIANT {
                0 => assert!(
                    <CurrentAleo as circuit::Environment>::is_satisfied(),
                    "Instruction '{operation}' should be satisfied (circuit): {literal_a}.{mode_a} {literal_a}.{mode_a}"
                ),
                1 => assert!(
                    <CurrentAleo as circuit::Environment>::is_satisfied(),
                    "Instruction '{operation}' should be satisfied (circuit): {literal_a}.{mode_a} {literal_a}.{mode_a}"
                ),
                _ => panic!("Found an invalid 'is' variant in the test"),
            }

            // Reset the circuit.
            <CurrentAleo as circuit::Environment>::reset();

            // Attempt to finalize the valid operand case.
            let mut registers = sample_finalize_registers(&stack, &function_name, &[literal_a, literal_a]).unwrap();
            operation.finalize(&stack, &mut registers).unwrap();

            // Retrieve the output.
            let output_c = registers.load_literal(&stack, &destination_operand).unwrap();

            // Ensure the output is correct.
            if let Literal::Boolean(output_c) = output_c {
                match VARIANT {
                    0 => assert!(*output_c, "Instruction '{operation}' failed (finalize): {literal_a} {literal_a}"),
                    1 => assert!(
                        !*output_c,
                        "Instruction '{operation}' should have failed (finalize): {literal_a} {literal_a}"
                    ),
                    _ => panic!("Found an invalid 'is' variant in the test"),
                }
            } else {
                panic!("The output must be a boolean (finalize)");
            }
        }
        /* Next, check the mismatching literals *fail*. */
        if literal_a != literal_b {
            // Attempt to compute the valid operand case.
            let values = [(literal_a, None), (literal_b, None)];
            let mut registers = sample_registers(&stack, &function_name, &values).unwrap();
            operation.evaluate(&stack, &mut registers).unwrap();

            // Retrieve the output.
            let output_a = registers.load_literal(&stack, &destination_operand).unwrap();

            // Ensure the output is correct.
            if let Literal::Boolean(output_a) = output_a {
                match VARIANT {
                    0 => assert!(
                        !*output_a,
                        "Instruction '{operation}' should have failed (console): {literal_a} {literal_b}"
                    ),
                    1 => assert!(*output_a, "Instruction '{operation}' failed (console): {literal_a} {literal_b}"),
                    _ => panic!("Found an invalid 'is' variant in the test"),
                }
            } else {
                panic!("The output must be a boolean (console)");
            }

            // Attempt to compute the valid operand case.
            let values = [(literal_a, Some(*mode_a)), (literal_b, Some(*mode_b))];
            let mut registers = sample_registers(&stack, &function_name, &values).unwrap();
            operation.execute::<CurrentAleo>(&stack, &mut registers).unwrap();

            // Retrieve the output.
            let output_b = registers.load_literal_circuit(&stack, &destination_operand).unwrap();

            // Ensure the output is correct.
            if let circuit::Literal::Boolean(output_b) = output_b {
                match VARIANT {
                    0 => assert!(
                        !output_b.eject_value(),
                        "Instruction '{operation}' failed (circuit): {literal_a}.{mode_a} {literal_b}.{mode_b}"
                    ),
                    1 => assert!(
                        output_b.eject_value(),
                        "Instruction '{operation}' should have failed (circuit): {literal_a}.{mode_a} {literal_b}.{mode_b}"
                    ),
                    _ => panic!("Found an invalid 'is' variant in the test"),
                }
            } else {
                panic!("The output must be a boolean (circuit)");
            }

            // Ensure the circuit is correct.
            match VARIANT {
                0 => assert!(
                    <CurrentAleo as circuit::Environment>::is_satisfied(),
                    "Instruction '{operation}' should be satisfied (circuit): {literal_a}.{mode_a} {literal_b}.{mode_b}"
                ),
                1 => assert!(
                    <CurrentAleo as circuit::Environment>::is_satisfied(),
                    "Instruction '{operation}' should be satisfied (circuit): {literal_a}.{mode_a} {literal_b}.{mode_b}"
                ),
                _ => panic!("Found an invalid 'is' variant in the test"),
            }

            // Reset the circuit.
            <CurrentAleo as circuit::Environment>::reset();

            // Attempt to finalize the valid operand case.
            let mut registers = sample_finalize_registers(&stack, &function_name, &[literal_a, literal_b]).unwrap();
            operation.finalize(&stack, &mut registers).unwrap();

            // Retrieve the output.
            let output_c = registers.load_literal(&stack, &destination_operand).unwrap();

            // Ensure the output is correct.
            if let Literal::Boolean(output_c) = output_c {
                match VARIANT {
                    0 => assert!(
                        !*output_c,
                        "Instruction '{operation}' should have failed (finalize): {literal_a} {literal_b}"
                    ),
                    1 => assert!(*output_c, "Instruction '{operation}' failed (finalize): {literal_a} {literal_b}"),
                    _ => panic!("Found an invalid 'is' variant in the test"),
                }
            } else {
                panic!("The output must be a boolean (finalize)");
            }
        }
    }

    fn check_is_fails(
        opcode: Opcode,
        literal_a: &Literal<CurrentNetwork>,
        literal_b: &Literal<CurrentNetwork>,
        mode_a: &circuit::Mode,
        mode_b: &circuit::Mode,
        cache: &mut HashMap<String, (ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)>,
    ) {
        // Initialize the types.
        let type_a = literal_a.to_type();
        let type_b = literal_b.to_type();
        assert_ne!(type_a, type_b, "The two literals must be *different* types for this test");

        // If the types mismatch, ensure the stack fails to initialize.
        let result = sample_stack(opcode, type_a, type_b, *mode_a, *mode_b, cache);
        assert!(
            result.is_err(),
            "Stack should have failed to initialize for: {opcode} {type_a}.{mode_a} {type_b}.{mode_b}"
        );
    }

    #[test]
    fn test_is_eq_succeeds() {
        // Initialize the operation.
        let operation = |operands, destination| IsEq::<CurrentNetwork> { operands, destination };
        // Initialize the opcode.
        let opcode = IsEq::<CurrentNetwork>::opcode();

        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let modes_a = [circuit::Mode::Public, circuit::Mode::Private];
        let modes_b = [circuit::Mode::Public, circuit::Mode::Private];

        // Prepare the key cache.
        let mut cache = Default::default();

        for _ in 0..ITERATIONS {
            let literals_a = crate::sample_literals!(CurrentNetwork, &mut rng);
            let literals_b = crate::sample_literals!(CurrentNetwork, &mut rng);
            for (literal_a, literal_b) in literals_a.iter().zip_eq(literals_b.iter()) {
                for mode_a in &modes_a {
                    for mode_b in &modes_b {
                        // Check the operation.
                        check_is(operation, opcode, literal_a, literal_b, mode_a, mode_b, &mut cache);
                    }
                }
            }
        }
    }

    #[test]
    fn test_is_eq_fails() {
        // Initialize the opcode.
        let opcode = IsEq::<CurrentNetwork>::opcode();

        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let modes_a = [circuit::Mode::Public, circuit::Mode::Private];
        let modes_b = [circuit::Mode::Public, circuit::Mode::Private];

        // Prepare the key cache.
        let mut cache = Default::default();

        for _ in 0..ITERATIONS {
            let literals_a = crate::sample_literals!(CurrentNetwork, &mut rng);
            let literals_b = crate::sample_literals!(CurrentNetwork, &mut rng);
            for literal_a in &literals_a {
                for literal_b in &literals_b {
                    if literal_a.to_type() != literal_b.to_type() {
                        for mode_a in &modes_a {
                            for mode_b in &modes_b {
                                // Check the operation fails.
                                check_is_fails(opcode, literal_a, literal_b, mode_a, mode_b, &mut cache);
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_is_neq_succeeds() {
        // Initialize the operation.
        let operation = |operands, destination| IsNeq::<CurrentNetwork> { operands, destination };
        // Initialize the opcode.
        let opcode = IsNeq::<CurrentNetwork>::opcode();

        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let modes_a = [circuit::Mode::Public, circuit::Mode::Private];
        let modes_b = [circuit::Mode::Public, circuit::Mode::Private];

        // Prepare the key cache.
        let mut cache = Default::default();

        for _ in 0..ITERATIONS {
            let literals_a = crate::sample_literals!(CurrentNetwork, &mut rng);
            let literals_b = crate::sample_literals!(CurrentNetwork, &mut rng);
            for (literal_a, literal_b) in literals_a.iter().zip_eq(literals_b.iter()) {
                for mode_a in &modes_a {
                    for mode_b in &modes_b {
                        // Check the operation.
                        check_is(operation, opcode, literal_a, literal_b, mode_a, mode_b, &mut cache);
                    }
                }
            }
        }
    }

    #[test]
    fn test_is_neq_fails() {
        // Initialize the opcode.
        let opcode = IsNeq::<CurrentNetwork>::opcode();

        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let modes_a = [circuit::Mode::Public, circuit::Mode::Private];
        let modes_b = [circuit::Mode::Public, circuit::Mode::Private];

        // Prepare the key cache.
        let mut cache = Default::default();

        for _ in 0..ITERATIONS {
            let literals_a = crate::sample_literals!(CurrentNetwork, &mut rng);
            let literals_b = crate::sample_literals!(CurrentNetwork, &mut rng);
            for literal_a in &literals_a {
                for literal_b in &literals_b {
                    if literal_a.to_type() != literal_b.to_type() {
                        for mode_a in &modes_a {
                            for mode_b in &modes_b {
                                // Check the operation fails.
                                check_is_fails(opcode, literal_a, literal_b, mode_a, mode_b, &mut cache);
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_parse() {
        let (string, is) = IsEq::<CurrentNetwork>::parse("is.eq r0 r1 into r2").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(is.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(is.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(is.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(is.destination, Register::Locator(2), "The destination register is incorrect");

        let (string, is) = IsNeq::<CurrentNetwork>::parse("is.neq r0 r1 into r2").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(is.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(is.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(is.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(is.destination, Register::Locator(2), "The destination register is incorrect");
    }
}
