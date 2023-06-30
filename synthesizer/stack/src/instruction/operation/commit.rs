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
};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType, Value},
};
use snarkvm_synthesizer_program::Operand;

/// BHP256 is a collision-resistant function that processes inputs in 256-bit chunks.
pub type CommitBHP256<N> = CommitInstruction<N, { Committer::CommitBHP256 as u8 }>;
/// BHP512 is a collision-resistant function that processes inputs in 512-bit chunks.
pub type CommitBHP512<N> = CommitInstruction<N, { Committer::CommitBHP512 as u8 }>;
/// BHP768 is a collision-resistant function that processes inputs in 768-bit chunks.
pub type CommitBHP768<N> = CommitInstruction<N, { Committer::CommitBHP768 as u8 }>;
/// BHP1024 is a collision-resistant function that processes inputs in 1024-bit chunks.
pub type CommitBHP1024<N> = CommitInstruction<N, { Committer::CommitBHP1024 as u8 }>;

/// Pedersen64 is a collision-resistant function that processes inputs in 64-bit chunks.
pub type CommitPED64<N> = CommitInstruction<N, { Committer::CommitPED64 as u8 }>;
/// Pedersen128 is a collision-resistant function that processes inputs in 128-bit chunks.
pub type CommitPED128<N> = CommitInstruction<N, { Committer::CommitPED128 as u8 }>;

enum Committer {
    CommitBHP256,
    CommitBHP512,
    CommitBHP768,
    CommitBHP1024,
    CommitPED64,
    CommitPED128,
}

/// Returns 'true' if the destination type is valid.
fn is_valid_destination_type(destination_type: LiteralType) -> bool {
    matches!(destination_type, LiteralType::Address | LiteralType::Field | LiteralType::Group)
}

/// Commits the operand into the declared type.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CommitInstruction<N: Network, const VARIANT: u8> {
    /// The operand as `input`.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
    /// The destination register type.
    destination_type: LiteralType,
}

impl<N: Network, const VARIANT: u8> CommitInstruction<N, VARIANT> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        match VARIANT {
            0 => Opcode::Commit("commit.bhp256"),
            1 => Opcode::Commit("commit.bhp512"),
            2 => Opcode::Commit("commit.bhp768"),
            3 => Opcode::Commit("commit.bhp1024"),
            4 => Opcode::Commit("commit.ped64"),
            5 => Opcode::Commit("commit.ped128"),
            6.. => panic!("Invalid 'commit' instruction opcode"),
        }
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that the operands is exactly two inputs.
        debug_assert!(self.operands.len() == 2, "Commit operations must have two operands");
        // Return the operands.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }

    /// Returns the destination register type.
    #[inline]
    pub const fn destination_type(&self) -> LiteralType {
        self.destination_type
    }
}

impl<N: Network, const VARIANT: u8> CommitInstruction<N, VARIANT> {
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
        // Ensure the destination type is valid.
        ensure!(is_valid_destination_type(self.destination_type), "Invalid destination type in 'commit' instruction");

        // Retrieve the input and randomizer.
        let input = registers.load(stack, &self.operands[0])?;
        let randomizer = registers.load(stack, &self.operands[1])?;
        // Retrieve the randomizer.
        let randomizer = match randomizer {
            Value::Plaintext(Plaintext::Literal(Literal::Scalar(randomizer), ..)) => randomizer,
            _ => bail!("Invalid randomizer type for the commit evaluation, expected a scalar"),
        };

        // Commit the input.
        let output = match VARIANT {
            0 => Literal::Group(N::commit_to_group_bhp256(&input.to_bits_le(), &randomizer)?),
            1 => Literal::Group(N::commit_to_group_bhp512(&input.to_bits_le(), &randomizer)?),
            2 => Literal::Group(N::commit_to_group_bhp768(&input.to_bits_le(), &randomizer)?),
            3 => Literal::Group(N::commit_to_group_bhp1024(&input.to_bits_le(), &randomizer)?),
            4 => Literal::Group(N::commit_to_group_ped64(&input.to_bits_le(), &randomizer)?),
            5 => Literal::Group(N::commit_to_group_ped128(&input.to_bits_le(), &randomizer)?),
            6.. => bail!("Invalid 'commit' variant: {VARIANT}"),
        };
        // Cast the output to the destination type.
        let output = output.downcast_lossy(self.destination_type)?;
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
        use circuit::ToBits;

        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Ensure the destination type is valid.
        ensure!(is_valid_destination_type(self.destination_type), "Invalid destination type in 'commit' instruction");

        // Retrieve the input and randomizer.
        let input = registers.load_circuit(stack, &self.operands[0])?;
        let randomizer = registers.load_circuit(stack, &self.operands[1])?;
        // Retrieve the randomizer.
        let randomizer = match randomizer {
            circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Scalar(randomizer), ..)) => {
                randomizer
            }
            _ => bail!("Invalid randomizer type for the commit execution, expected a scalar"),
        };

        // Commits the input.
        let output = match VARIANT {
            0 => circuit::Literal::Group(A::commit_to_group_bhp256(&input.to_bits_le(), &randomizer)),
            1 => circuit::Literal::Group(A::commit_to_group_bhp512(&input.to_bits_le(), &randomizer)),
            2 => circuit::Literal::Group(A::commit_to_group_bhp768(&input.to_bits_le(), &randomizer)),
            3 => circuit::Literal::Group(A::commit_to_group_bhp1024(&input.to_bits_le(), &randomizer)),
            4 => circuit::Literal::Group(A::commit_to_group_ped64(&input.to_bits_le(), &randomizer)),
            5 => circuit::Literal::Group(A::commit_to_group_ped128(&input.to_bits_le(), &randomizer)),
            6.. => bail!("Invalid 'commit' variant: {VARIANT}"),
        };
        let output = output.downcast_lossy(self.destination_type)?;
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
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Ensure the destination type is valid.
        ensure!(is_valid_destination_type(self.destination_type), "Invalid destination type in 'commit' instruction");

        // TODO (howardwu): If the operation is Pedersen, check that it is within the number of bits.

        match VARIANT {
            0..=5 => Ok(vec![RegisterType::Plaintext(PlaintextType::Literal(self.destination_type))]),
            6.. => bail!("Invalid 'commit' variant: {VARIANT}"),
        }
    }
}

impl<N: Network, const VARIANT: u8> Parser for CommitInstruction<N, VARIANT> {
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
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "as" from the string.
        let (string, _) = tag("as")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register type from the string.
        let (string, destination_type) = LiteralType::parse(string)?;
        // Ensure the destination type is allowed.
        match destination_type {
            LiteralType::Address | LiteralType::Field | LiteralType::Group => {
                Ok((string, Self { operands: vec![first, second], destination, destination_type }))
            }
            _ => map_res(fail, |_: ParserResult<Self>| {
                Err(error(format!("Failed to parse 'commit': '{destination_type}' is invalid")))
            })(string),
        }
    }
}

impl<N: Network, const VARIANT: u8> FromStr for CommitInstruction<N, VARIANT> {
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

impl<N: Network, const VARIANT: u8> Debug for CommitInstruction<N, VARIANT> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, const VARIANT: u8> Display for CommitInstruction<N, VARIANT> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{operand} "))?;
        write!(f, "into {} as {}", self.destination, self.destination_type)
    }
}

impl<N: Network, const VARIANT: u8> FromBytes for CommitInstruction<N, VARIANT> {
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
        // Read the destination register type.
        let destination_type = LiteralType::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self { operands, destination, destination_type })
    }
}

impl<N: Network, const VARIANT: u8> ToBytes for CommitInstruction<N, VARIANT> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(error(format!("The number of operands must be 2, found {}", self.operands.len())));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer)?;
        // Write the destination register type.
        self.destination_type.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instruction::test_helpers::{sample_finalize_registers, sample_registers};
    use circuit::{AleoV0, Eject};
    use console::{network::Testnet3, program::Identifier};
    use snarkvm_synthesizer_snark::{ProvingKey, VerifyingKey};
    use synthesizer::process::Stack;

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
        destination_type: LiteralType,
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
                {opcode} {r0} {r1} into {r2} as {destination_type};
                finalize {r0} {r1};

            finalize {function_name}:
                input {r0} as {type_a}.public;
                input {r1} as {type_b}.public;
                {opcode} {r0} {r1} into {r2} as {destination_type};
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

    fn check_commit<const VARIANT: u8>(
        operation: impl FnOnce(
            Vec<Operand<CurrentNetwork>>,
            Register<CurrentNetwork>,
            LiteralType,
        ) -> CommitInstruction<CurrentNetwork, VARIANT>,
        opcode: Opcode,
        literal_a: &Literal<CurrentNetwork>,
        literal_b: &Literal<CurrentNetwork>,
        mode_a: &circuit::Mode,
        mode_b: &circuit::Mode,
        destination_type: LiteralType,
        cache: &mut HashMap<String, (ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)>,
    ) {
        println!("Checking '{opcode}' for '{literal_a}.{mode_a}' and '{literal_b}.{mode_b}'");

        // Initialize the types.
        let type_a = literal_a.to_type();
        let type_b = literal_b.to_type();

        // Initialize the stack.
        let (stack, operands, destination) =
            sample_stack(opcode, type_a, type_b, *mode_a, *mode_b, destination_type, cache).unwrap();
        // Initialize the operation.
        let operation = operation(operands, destination.clone(), destination_type);
        // Initialize the function name.
        let function_name = Identifier::from_str("run").unwrap();
        // Initialize a destination operand.
        let destination_operand = Operand::Register(destination);

        // Attempt to evaluate the valid operand case.
        let values = [(literal_a, None), (literal_b, None)];
        let mut evaluate_registers = sample_registers(&stack, &function_name, &values).unwrap();
        let result_a = operation.evaluate(&stack, &mut evaluate_registers);

        // Attempt to execute the valid operand case.
        let values = [(literal_a, Some(*mode_a)), (literal_b, Some(*mode_b))];
        let mut execute_registers = sample_registers(&stack, &function_name, &values).unwrap();
        let result_b = operation.execute::<CurrentAleo>(&stack, &mut execute_registers);

        // Attempt to finalize the valid operand case.
        let mut finalize_registers =
            sample_finalize_registers(&stack, &function_name, &[literal_a, literal_b]).unwrap();
        let result_c = operation.finalize(&stack, &mut finalize_registers);

        // Check that either all operations failed, or all operations succeeded.
        let all_failed = result_a.is_err() && result_b.is_err() && result_c.is_err();
        let all_succeeded = result_a.is_ok() && result_b.is_ok() && result_c.is_ok();
        assert!(
            all_failed || all_succeeded,
            "The results of the evaluation, execution, and finalization should either all succeed or all fail"
        );

        // If all operations succeeded, check that the outputs are consistent.
        if all_succeeded {
            // Retrieve the output of evaluation.
            let output_a = evaluate_registers.load(&stack, &destination_operand).unwrap();

            // Retrieve the output of execution.
            let output_b = execute_registers.load_circuit(&stack, &destination_operand).unwrap();

            // Retrieve the output of finalization.
            let output_c = finalize_registers.load(&stack, &destination_operand).unwrap();

            // Check that the outputs are consistent.
            assert_eq!(
                output_a,
                output_b.eject_value(),
                "The results of the evaluation and execution are inconsistent"
            );
            assert_eq!(output_a, output_c, "The results of the evaluation and finalization are inconsistent");

            // Check that the output type is consistent with the declared type.
            match output_a {
                Value::Plaintext(Plaintext::Literal(literal, _)) => {
                    assert_eq!(
                        literal.to_type(),
                        destination_type,
                        "The output type is inconsistent with the declared type"
                    );
                }
                _ => unreachable!("The output type is inconsistent with the declared type"),
            }
        }

        // Reset the circuit.
        <CurrentAleo as circuit::Environment>::reset();
    }

    fn valid_destination_types() -> &'static [LiteralType] {
        &[LiteralType::Address, LiteralType::Field, LiteralType::Group]
    }

    macro_rules! test_commit {
        ($name: tt, $commit:ident) => {
            paste::paste! {
                #[test]
                fn [<test _ $name _ is _ consistent>]() {
                    // Initialize the operation.
                    let operation = |operands, destination, destination_type| $commit::<CurrentNetwork> { operands, destination, destination_type };
                    // Initialize the opcode.
                    let opcode = $commit::<CurrentNetwork>::opcode();

                    // Prepare the rng.
                    let mut rng = TestRng::default();

                   // Prepare the test.
                    let modes_a = [circuit::Mode::Public, circuit::Mode::Private];
                    let modes_b = [circuit::Mode::Public, circuit::Mode::Private];

                    // Prepare the key cache.
                    let mut cache = Default::default();

                    for _ in 0..ITERATIONS {
                        let literals_a = crate::sample_literals!(CurrentNetwork, &mut rng);
                        let literals_b = vec![console::program::Literal::Scalar(console::types::Scalar::rand(&mut rng))];

                        for literal_a in &literals_a {
                            for literal_b in &literals_b {
                                for mode_a in &modes_a {
                                    for mode_b in &modes_b {
                                        for destination_type in valid_destination_types() {
                                            check_commit(operation, opcode, literal_a, literal_b, mode_a, mode_b, *destination_type, &mut cache);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        };
    }

    test_commit!(commit_bhp256, CommitBHP256);
    test_commit!(commit_bhp512, CommitBHP512);
    test_commit!(commit_bhp768, CommitBHP768);
    test_commit!(commit_bhp1024, CommitBHP1024);

    // Note this test must be explicitly written, instead of using the macro, because CommitPED64 and CommitToGroupPED64 fails on certain input types.
    #[test]
    fn test_commit_ped64_is_consistent() {
        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let modes_a = [circuit::Mode::Public, circuit::Mode::Private];
        let modes_b = [circuit::Mode::Public, circuit::Mode::Private];

        macro_rules! check_commit {
            ($operation:tt) => {
                let mut cache = Default::default();
                for _ in 0..ITERATIONS {
                    let literals_a = [
                        Literal::Boolean(console::types::Boolean::rand(&mut rng)),
                        Literal::I8(console::types::I8::rand(&mut rng)),
                        Literal::I16(console::types::I16::rand(&mut rng)),
                        Literal::I32(console::types::I32::rand(&mut rng)),
                        Literal::U8(console::types::U8::rand(&mut rng)),
                        Literal::U16(console::types::U16::rand(&mut rng)),
                        Literal::U32(console::types::U32::rand(&mut rng)),
                    ];
                    let literals_b = vec![Literal::Scalar(console::types::Scalar::rand(&mut rng))];
                    for literal_a in &literals_a {
                        for literal_b in &literals_b {
                            for mode_a in &modes_a {
                                for mode_b in &modes_b {
                                    for destination_type in valid_destination_types() {
                                        check_commit(
                                            |operands, destination, destination_type| $operation::<CurrentNetwork> {
                                                operands,
                                                destination,
                                                destination_type,
                                            },
                                            $operation::<CurrentNetwork>::opcode(),
                                            literal_a,
                                            literal_b,
                                            mode_a,
                                            mode_b,
                                            *destination_type,
                                            &mut cache,
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            };
        }
        check_commit!(CommitPED64);
    }

    // Note this test must be explicitly written, instead of using the macro, because CommitPED128 and CommitToGroupPED64 fails on certain input types.
    #[test]
    fn test_commit_ped128_is_consistent() {
        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let modes_a = [circuit::Mode::Public, circuit::Mode::Private];
        let modes_b = [circuit::Mode::Public, circuit::Mode::Private];

        macro_rules! check_commit {
            ($operation:tt) => {
                let mut cache = Default::default();
                for _ in 0..ITERATIONS {
                    let literals_a = [
                        Literal::Boolean(console::types::Boolean::rand(&mut rng)),
                        Literal::I8(console::types::I8::rand(&mut rng)),
                        Literal::I16(console::types::I16::rand(&mut rng)),
                        Literal::I32(console::types::I32::rand(&mut rng)),
                        Literal::I64(console::types::I64::rand(&mut rng)),
                        Literal::U8(console::types::U8::rand(&mut rng)),
                        Literal::U16(console::types::U16::rand(&mut rng)),
                        Literal::U32(console::types::U32::rand(&mut rng)),
                        Literal::U64(console::types::U64::rand(&mut rng)),
                    ];
                    let literals_b = vec![Literal::Scalar(console::types::Scalar::rand(&mut rng))];
                    for literal_a in &literals_a {
                        for literal_b in &literals_b {
                            for mode_a in &modes_a {
                                for mode_b in &modes_b {
                                    for destination_type in valid_destination_types() {
                                        check_commit(
                                            |operands, destination, destination_type| $operation::<CurrentNetwork> {
                                                operands,
                                                destination,
                                                destination_type,
                                            },
                                            $operation::<CurrentNetwork>::opcode(),
                                            literal_a,
                                            literal_b,
                                            mode_a,
                                            mode_b,
                                            *destination_type,
                                            &mut cache,
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            };
        }
        check_commit!(CommitPED128);
    }

    #[test]
    fn test_parse() {
        for destination_type in valid_destination_types() {
            let instruction = format!("commit.bhp512 r0 r1 into r2 as {destination_type}");
            let (string, commit) = CommitBHP512::<CurrentNetwork>::parse(&instruction).unwrap();
            assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
            assert_eq!(commit.operands.len(), 2, "The number of operands is incorrect");
            assert_eq!(commit.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
            assert_eq!(commit.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
            assert_eq!(commit.destination, Register::Locator(2), "The destination register is incorrect");
            assert_eq!(commit.destination_type, *destination_type, "The destination type is incorrect");
        }
    }
}
