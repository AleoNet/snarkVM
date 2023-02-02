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

use crate::{Opcode, Operand, Registers, Stack};
use console::{
    network::prelude::*,
    program::{Register, RegisterType},
};

/// Asserts two operands are equal to each other.
pub type AssertEq<N> = AssertInstruction<N, { Variant::AssertEq as u8 }>;
/// Asserts two operands are **not** equal to each other.
pub type AssertNeq<N> = AssertInstruction<N, { Variant::AssertNeq as u8 }>;

enum Variant {
    AssertEq,
    AssertNeq,
}

/// Asserts an operation on two operands.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AssertInstruction<N: Network, const VARIANT: u8> {
    /// The operands.
    operands: Vec<Operand<N>>,
}

impl<N: Network, const VARIANT: u8> AssertInstruction<N, VARIANT> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        match VARIANT {
            0 => Opcode::Assert("assert.eq"),
            1 => Opcode::Assert("assert.neq"),
            _ => panic!("Invalid 'assert' instruction opcode"),
        }
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that the operands is exactly two inputs.
        debug_assert!(self.operands.len() == 2, "Assert operations must have two operands");
        // Return the operands.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![]
    }
}

impl<N: Network, const VARIANT: u8> AssertInstruction<N, VARIANT> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the inputs.
        let input_a = registers.load(stack, &self.operands[0])?;
        let input_b = registers.load(stack, &self.operands[1])?;

        // Assert the inputs.
        match VARIANT {
            0 => {
                if input_a != input_b {
                    bail!("'{}' failed: '{input_a}' is not equal to '{input_b}' (should be equal)", Self::opcode())
                }
            }
            1 => {
                if input_a == input_b {
                    bail!("'{}' failed: '{input_a}' is equal to '{input_b}' (should not be equal)", Self::opcode())
                }
            }
            _ => bail!("Invalid 'assert' variant: {VARIANT}"),
        }
        Ok(())
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the inputs.
        let input_a = registers.load_circuit(stack, &self.operands[0])?;
        let input_b = registers.load_circuit(stack, &self.operands[1])?;

        // Assert the inputs.
        match VARIANT {
            0 => A::assert(input_a.is_equal(&input_b)),
            1 => A::assert(input_a.is_not_equal(&input_b)),
            _ => bail!("Invalid 'assert' variant: {VARIANT}"),
        }
        Ok(())
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(&self, _stack: &Stack<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
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
            0 | 1 => Ok(vec![]),
            _ => bail!("Invalid 'assert' variant: {VARIANT}"),
        }
    }
}

impl<N: Network, const VARIANT: u8> Parser for AssertInstruction<N, VARIANT> {
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

        Ok((string, Self { operands: vec![first, second] }))
    }
}

impl<N: Network, const VARIANT: u8> FromStr for AssertInstruction<N, VARIANT> {
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

impl<N: Network, const VARIANT: u8> Debug for AssertInstruction<N, VARIANT> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, const VARIANT: u8> Display for AssertInstruction<N, VARIANT> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            eprintln!("The number of operands must be 2, found {}", self.operands.len());
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{} ", operand))
    }
}

impl<N: Network, const VARIANT: u8> FromBytes for AssertInstruction<N, VARIANT> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(2);
        // Read the operands.
        for _ in 0..2 {
            operands.push(Operand::read_le(&mut reader)?);
        }

        // Return the operation.
        Ok(Self { operands })
    }
}

impl<N: Network, const VARIANT: u8> ToBytes for AssertInstruction<N, VARIANT> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(error(format!("The number of operands must be 2, found {}", self.operands.len())));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ProvingKey, VerifyingKey};
    use circuit::AleoV0;
    use console::{
        network::Testnet3,
        program::{Literal, LiteralType},
    };

    use std::collections::HashMap;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    /// Samples the stack. Note: Do not replicate this for real program use, it is insecure.
    fn sample_stack(
        opcode: Opcode,
        type_a: LiteralType,
        type_b: LiteralType,
        mode_a: circuit::Mode,
        mode_b: circuit::Mode,
        cache: &mut HashMap<String, (ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)>,
    ) -> Result<(Stack<CurrentNetwork>, Vec<Operand<CurrentNetwork>>)> {
        use crate::{Process, Program};
        use console::program::Identifier;

        // Initialize the opcode.
        let opcode = opcode.to_string();

        // Initialize the function name.
        let function_name = Identifier::<CurrentNetwork>::from_str("run")?;

        // Initialize the registers.
        let r0 = Register::Locator(0);
        let r1 = Register::Locator(1);

        // Initialize the program.
        let program = Program::from_str(&format!(
            "program testing.aleo;
            function {function_name}:
                input {r0} as {type_a}.{mode_a};
                input {r1} as {type_b}.{mode_b};
                {opcode} {r0} {r1};
        "
        ))?;

        // Initialize the operands.
        let operand_a = Operand::Register(r0);
        let operand_b = Operand::Register(r1);
        let operands = vec![operand_a, operand_b];

        // Initialize the stack.
        let stack = Stack::new(&Process::load_with_cache(cache)?, &program)?;

        Ok((stack, operands))
    }

    /// Samples the registers. Note: Do not replicate this for real program use, it is insecure.
    fn sample_registers(
        stack: &Stack<CurrentNetwork>,
        literal_a: &Literal<CurrentNetwork>,
        literal_b: &Literal<CurrentNetwork>,
        mode_a: Option<circuit::Mode>,
        mode_b: Option<circuit::Mode>,
    ) -> Result<Registers<CurrentNetwork, CurrentAleo>> {
        use crate::{Authorization, CallStack};
        use console::program::{Identifier, Plaintext, Value};

        // Initialize the function name.
        let function_name = Identifier::from_str("run")?;

        // Initialize the registers.
        let mut registers = Registers::<CurrentNetwork, CurrentAleo>::new(
            CallStack::evaluate(Authorization::new(&[]))?,
            stack.get_register_types(&function_name)?.clone(),
        );

        // Initialize the registers.
        let r0 = Register::Locator(0);
        let r1 = Register::Locator(1);

        // Initialize the console values.
        let value_a = Value::Plaintext(Plaintext::from(literal_a));
        let value_b = Value::Plaintext(Plaintext::from(literal_b));

        // Store the values in the console registers.
        registers.store(stack, &r0, value_a.clone())?;
        registers.store(stack, &r1, value_b.clone())?;

        if let (Some(mode_a), Some(mode_b)) = (mode_a, mode_b) {
            use circuit::Inject;

            // Initialize the circuit values.
            let circuit_a = circuit::Value::new(mode_a, value_a);
            let circuit_b = circuit::Value::new(mode_b, value_b);

            // Store the values in the circuit registers.
            registers.store_circuit(stack, &r0, circuit_a)?;
            registers.store_circuit(stack, &r1, circuit_b)?;
        }

        Ok(registers)
    }

    fn check_assert<const VARIANT: u8>(
        operation: impl FnOnce(Vec<Operand<CurrentNetwork>>) -> AssertInstruction<CurrentNetwork, VARIANT>,
        opcode: Opcode,
        literal_a: &Literal<CurrentNetwork>,
        literal_b: &Literal<CurrentNetwork>,
        mode_a: &circuit::Mode,
        mode_b: &circuit::Mode,
        cache: &mut HashMap<String, (ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)>,
    ) {
        println!("Checking '{opcode}' for '{literal_a}.{mode_a}' and '{literal_b}.{mode_b}'");

        // Initialize the types.
        let type_a = literal_a.to_type();
        let type_b = literal_b.to_type();
        assert_eq!(type_a, type_b, "The two literals must be the *same* type for this test");

        // Initialize the stack.
        let (stack, operands) = sample_stack(opcode, type_a, type_b, *mode_a, *mode_b, cache).unwrap();
        // Initialize the operation.
        let operation = operation(operands);

        /* First, check the operation *succeeds* when both operands are `literal_a.mode_a`. */
        {
            // Attempt to compute the valid operand case.
            let mut registers = sample_registers(&stack, literal_a, literal_a, None, None).unwrap();
            let result_a = operation.evaluate(&stack, &mut registers);

            // Ensure the result is correct.
            match VARIANT {
                0 => assert!(result_a.is_ok(), "Instruction '{operation}' failed (console): {literal_a} {literal_a}"),
                1 => assert!(
                    result_a.is_err(),
                    "Instruction '{operation}' should have failed (console): {literal_a} {literal_a}"
                ),
                _ => panic!("Found an invalid 'assert' variant in the test"),
            }

            // Attempt to compute the valid operand case.
            let mut registers = sample_registers(&stack, literal_a, literal_a, Some(*mode_a), Some(*mode_a)).unwrap();
            let result_b = operation.execute::<CurrentAleo>(&stack, &mut registers);

            // Ensure the result is correct.
            match VARIANT {
                0 => assert!(
                    result_b.is_ok(),
                    "Instruction '{operation}' failed (circuit): {literal_a}.{mode_a} {literal_a}.{mode_a}"
                ),
                1 => assert!(
                    result_b.is_ok(), // <- 'is_ok()' is correct! The circuit should execute, but the constraint should not be satisfied.
                    "Instruction '{operation}' should not have panicked (circuit): {literal_a}.{mode_a} {literal_a}.{mode_a}"
                ),
                _ => panic!("Found an invalid 'assert' variant in the test"),
            }

            // Ensure the circuit is correct.
            match VARIANT {
                0 => assert!(
                    <CurrentAleo as circuit::Environment>::is_satisfied(),
                    "Instruction '{operation}' should be satisfied (circuit): {literal_a}.{mode_a} {literal_a}.{mode_a}"
                ),
                1 => assert!(
                    !<CurrentAleo as circuit::Environment>::is_satisfied(),
                    "Instruction '{operation}' should not be satisfied (circuit): {literal_a}.{mode_a} {literal_a}.{mode_a}"
                ),
                _ => panic!("Found an invalid 'assert' variant in the test"),
            }

            // Reset the circuit.
            <CurrentAleo as circuit::Environment>::reset();
        }
        /* Next, check the mismatching literals *fail*. */
        if literal_a != literal_b {
            // Attempt to compute the valid operand case.
            let mut registers = sample_registers(&stack, literal_a, literal_b, None, None).unwrap();
            let result_a = operation.evaluate(&stack, &mut registers);

            // Ensure the result is correct.
            match VARIANT {
                0 => assert!(
                    result_a.is_err(),
                    "Instruction '{operation}' should have failed (console): {literal_a} {literal_b}"
                ),
                1 => assert!(result_a.is_ok(), "Instruction '{operation}' failed (console): {literal_a} {literal_b}"),
                _ => panic!("Found an invalid 'assert' variant in the test"),
            }

            // Attempt to compute the valid operand case.
            let mut registers = sample_registers(&stack, literal_a, literal_b, Some(*mode_a), Some(*mode_b)).unwrap();
            let result_b = operation.execute::<CurrentAleo>(&stack, &mut registers);

            // Ensure the result is correct.
            match VARIANT {
                0 => assert!(
                    result_b.is_ok(), // <- 'is_ok()' is correct! The circuit should execute, but the constraint should not be satisfied.
                    "Instruction '{operation}' should not have panicked (circuit): {literal_a}.{mode_a} {literal_b}.{mode_b}"
                ),
                1 => assert!(
                    result_b.is_ok(),
                    "Instruction '{operation}' failed (circuit): {literal_a}.{mode_a} {literal_b}.{mode_b}"
                ),
                _ => panic!("Found an invalid 'assert' variant in the test"),
            }

            // Ensure the circuit is correct.
            match VARIANT {
                0 => assert!(
                    !<CurrentAleo as circuit::Environment>::is_satisfied(),
                    "Instruction '{operation}' should not be satisfied (circuit): {literal_a}.{mode_a} {literal_b}.{mode_b}"
                ),
                1 => assert!(
                    <CurrentAleo as circuit::Environment>::is_satisfied(),
                    "Instruction '{operation}' should be satisfied (circuit): {literal_a}.{mode_a} {literal_b}.{mode_b}"
                ),
                _ => panic!("Found an invalid 'assert' variant in the test"),
            }

            // Reset the circuit.
            <CurrentAleo as circuit::Environment>::reset();
        }
    }

    fn check_assert_fails(
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
    fn test_assert_eq_succeeds() {
        // Initialize the operation.
        let operation = |operands| AssertEq::<CurrentNetwork> { operands };
        // Initialize the opcode.
        let opcode = AssertEq::<CurrentNetwork>::opcode();

        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let literals_a = crate::sample_literals!(CurrentNetwork, &mut rng);
        let literals_b = crate::sample_literals!(CurrentNetwork, &mut rng);
        let modes_a = [/* circuit::Mode::Constant, */ circuit::Mode::Public, circuit::Mode::Private];
        let modes_b = [/* circuit::Mode::Constant, */ circuit::Mode::Public, circuit::Mode::Private];

        // Prepare the key cache.
        let mut cache = Default::default();

        for (literal_a, literal_b) in literals_a.iter().zip_eq(literals_b.iter()) {
            for mode_a in &modes_a {
                for mode_b in &modes_b {
                    // Check the operation.
                    check_assert(operation, opcode, literal_a, literal_b, mode_a, mode_b, &mut cache);
                }
            }
        }
    }

    #[test]
    fn test_assert_eq_fails() {
        // Initialize the opcode.
        let opcode = AssertEq::<CurrentNetwork>::opcode();

        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let literals_a = crate::sample_literals!(CurrentNetwork, &mut rng);
        let literals_b = crate::sample_literals!(CurrentNetwork, &mut rng);
        let modes_a = [/* circuit::Mode::Constant, */ circuit::Mode::Public, circuit::Mode::Private];
        let modes_b = [/* circuit::Mode::Constant, */ circuit::Mode::Public, circuit::Mode::Private];

        // Prepare the key cache.
        let mut cache = Default::default();

        for literal_a in &literals_a {
            for literal_b in &literals_b {
                if literal_a.to_type() != literal_b.to_type() {
                    for mode_a in &modes_a {
                        for mode_b in &modes_b {
                            // Check the operation fails.
                            check_assert_fails(opcode, literal_a, literal_b, mode_a, mode_b, &mut cache);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_assert_neq_succeeds() {
        // Initialize the operation.
        let operation = |operands| AssertNeq::<CurrentNetwork> { operands };
        // Initialize the opcode.
        let opcode = AssertNeq::<CurrentNetwork>::opcode();

        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let literals_a = crate::sample_literals!(CurrentNetwork, &mut rng);
        let literals_b = crate::sample_literals!(CurrentNetwork, &mut rng);
        let modes_a = [/* circuit::Mode::Constant, */ circuit::Mode::Public, circuit::Mode::Private];
        let modes_b = [/* circuit::Mode::Constant, */ circuit::Mode::Public, circuit::Mode::Private];

        // Prepare the key cache.
        let mut cache = Default::default();

        for (literal_a, literal_b) in literals_a.iter().zip_eq(literals_b.iter()) {
            for mode_a in &modes_a {
                for mode_b in &modes_b {
                    // Check the operation.
                    check_assert(operation, opcode, literal_a, literal_b, mode_a, mode_b, &mut cache);
                }
            }
        }
    }

    #[test]
    fn test_assert_neq_fails() {
        // Initialize the opcode.
        let opcode = AssertNeq::<CurrentNetwork>::opcode();

        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let literals_a = crate::sample_literals!(CurrentNetwork, &mut rng);
        let literals_b = crate::sample_literals!(CurrentNetwork, &mut rng);
        let modes_a = [/* circuit::Mode::Constant, */ circuit::Mode::Public, circuit::Mode::Private];
        let modes_b = [/* circuit::Mode::Constant, */ circuit::Mode::Public, circuit::Mode::Private];

        // Prepare the key cache.
        let mut cache = Default::default();

        for literal_a in &literals_a {
            for literal_b in &literals_b {
                if literal_a.to_type() != literal_b.to_type() {
                    for mode_a in &modes_a {
                        for mode_b in &modes_b {
                            // Check the operation fails.
                            check_assert_fails(opcode, literal_a, literal_b, mode_a, mode_b, &mut cache);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_parse() {
        let (string, assert) = AssertEq::<CurrentNetwork>::parse("assert.eq r0 r1").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(assert.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(assert.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(assert.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");

        let (string, assert) = AssertNeq::<CurrentNetwork>::parse("assert.neq r0 r1").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(assert.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(assert.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(assert.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
    }
}
