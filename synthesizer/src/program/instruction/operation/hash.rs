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
    Opcode,
    Operand,
    RegistersLoad,
    RegistersLoadCircuit,
    RegistersStore,
    RegistersStoreCircuit,
    StackMatches,
    StackProgram,
};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType, Value},
};

/// BHP256 is a collision-resistant hash function that processes inputs in 256-bit chunks.
pub type HashBHP256<N> = HashInstruction<N, { Hasher::BHP256 as u8 }>;
/// BHP512 is a collision-resistant hash function that processes inputs in 512-bit chunks.
pub type HashBHP512<N> = HashInstruction<N, { Hasher::BHP512 as u8 }>;
/// BHP768 is a collision-resistant hash function that processes inputs in 768-bit chunks.
pub type HashBHP768<N> = HashInstruction<N, { Hasher::BHP768 as u8 }>;
/// BHP1024 is a collision-resistant hash function that processes inputs in 1024-bit chunks.
pub type HashBHP1024<N> = HashInstruction<N, { Hasher::BHP1024 as u8 }>;

/// Pedersen64 is a collision-resistant hash function that processes inputs in 64-bit chunks.
pub type HashPED64<N> = HashInstruction<N, { Hasher::PED64 as u8 }>;
/// Pedersen128 is a collision-resistant hash function that processes inputs in 128-bit chunks.
pub type HashPED128<N> = HashInstruction<N, { Hasher::PED128 as u8 }>;

/// Poseidon2 is a cryptographic hash function that processes inputs in 2-field chunks.
pub type HashPSD2<N> = HashInstruction<N, { Hasher::PSD2 as u8 }>;
/// Poseidon4 is a cryptographic hash function that processes inputs in 4-field chunks.
pub type HashPSD4<N> = HashInstruction<N, { Hasher::PSD4 as u8 }>;
/// Poseidon8 is a cryptographic hash function that processes inputs in 8-field chunks.
pub type HashPSD8<N> = HashInstruction<N, { Hasher::PSD8 as u8 }>;

enum Hasher {
    BHP256,
    BHP512,
    BHP768,
    BHP1024,
    PED64,
    PED128,
    PSD2,
    PSD4,
    PSD8,
}

/// Hashes the operand into the declared type.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct HashInstruction<N: Network, const VARIANT: u8> {
    /// The operand as `input`.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network, const VARIANT: u8> HashInstruction<N, VARIANT> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        match VARIANT {
            0 => Opcode::Hash("hash.bhp256"),
            1 => Opcode::Hash("hash.bhp512"),
            2 => Opcode::Hash("hash.bhp768"),
            3 => Opcode::Hash("hash.bhp1024"),
            4 => Opcode::Hash("hash.ped64"),
            5 => Opcode::Hash("hash.ped128"),
            6 => Opcode::Hash("hash.psd2"),
            7 => Opcode::Hash("hash.psd4"),
            8 => Opcode::Hash("hash.psd8"),
            _ => panic!("Invalid 'hash' instruction opcode"),
        }
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that the operands is exactly one input.
        debug_assert!(self.operands.len() == 1, "Hash operation must have one operand");
        // Return the operand.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }
}

impl<N: Network, const VARIANT: u8> HashInstruction<N, VARIANT> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Load the operand.
        let input = registers.load(stack, &self.operands[0])?;
        // Hash the input.
        let output = match VARIANT {
            0 => N::hash_bhp256(&input.to_bits_le())?,
            1 => N::hash_bhp512(&input.to_bits_le())?,
            2 => N::hash_bhp768(&input.to_bits_le())?,
            3 => N::hash_bhp1024(&input.to_bits_le())?,
            4 => N::hash_ped64(&input.to_bits_le())?,
            5 => N::hash_ped128(&input.to_bits_le())?,
            6 => N::hash_psd2(&input.to_fields()?)?,
            7 => N::hash_psd4(&input.to_fields()?)?,
            8 => N::hash_psd8(&input.to_fields()?)?,
            _ => bail!("Invalid 'hash' variant: {VARIANT}"),
        };
        // Store the output.
        registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(Literal::Field(output))))
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoadCircuit<N, A> + RegistersStoreCircuit<N, A>),
    ) -> Result<()> {
        use circuit::{ToBits, ToFields};

        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Load the operand.
        let input = registers.load_circuit(stack, &self.operands[0])?;
        // Hash the input.
        let output = match VARIANT {
            0 => A::hash_bhp256(&input.to_bits_le()),
            1 => A::hash_bhp512(&input.to_bits_le()),
            2 => A::hash_bhp768(&input.to_bits_le()),
            3 => A::hash_bhp1024(&input.to_bits_le()),
            4 => A::hash_ped64(&input.to_bits_le()),
            5 => A::hash_ped128(&input.to_bits_le()),
            6 => A::hash_psd2(&input.to_fields()),
            7 => A::hash_psd4(&input.to_fields()),
            8 => A::hash_psd8(&input.to_fields()),
            _ => bail!("Invalid 'hash' variant: {VARIANT}"),
        };
        // Convert the output to a stack value.
        let output =
            circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Field(output), Default::default()));
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
        if input_types.len() != 1 {
            bail!("Instruction '{}' expects 1 inputs, found {} inputs", Self::opcode(), input_types.len())
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // TODO (howardwu): If the operation is Pedersen, check that it is within the number of bits.

        match VARIANT {
            0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => {
                Ok(vec![RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field))])
            }
            _ => bail!("Invalid 'hash' variant: {VARIANT}"),
        }
    }
}

impl<N: Network, const VARIANT: u8> Parser for HashInstruction<N, VARIANT> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the operand from the string.
        let (string, operand) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        Ok((string, Self { operands: vec![operand], destination }))
    }
}

impl<N: Network, const VARIANT: u8> FromStr for HashInstruction<N, VARIANT> {
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

impl<N: Network, const VARIANT: u8> Debug for HashInstruction<N, VARIANT> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, const VARIANT: u8> Display for HashInstruction<N, VARIANT> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 1.
        if self.operands.len() != 1 {
            eprintln!("The number of operands must be 1, found {}", self.operands.len());
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{operand} "))?;
        write!(f, "into {}", self.destination)
    }
}

impl<N: Network, const VARIANT: u8> FromBytes for HashInstruction<N, VARIANT> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the operand.
        let operands = vec![Operand::read_le(&mut reader)?];
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;
        // Return the operation.
        Ok(Self { operands, destination })
    }
}

impl<N: Network, const VARIANT: u8> ToBytes for HashInstruction<N, VARIANT> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 1.
        if self.operands.len() != 1 {
            return Err(error(format!("The number of operands must be 1, found {}", self.operands.len())));
        }
        // Write the operand.
        self.operands[0].write_le(&mut writer)?;
        // Write the destination register.
        self.destination.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        process::Stack,
        program::test_helpers::{sample_finalize_registers, sample_registers},
    };
    use circuit::{AleoV0, Eject};
    use console::{network::Testnet3, program::Identifier};
    use snarkvm_synthesizer_snark::{ProvingKey, VerifyingKey};

    use std::collections::HashMap;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    const ITERATIONS: usize = 100;

    /// Samples the stack. Note: Do not replicate this for real program use, it is insecure.
    #[allow(clippy::type_complexity)]
    fn sample_stack(
        opcode: Opcode,
        type_: LiteralType,
        mode: circuit::Mode,
        cache: &mut HashMap<String, (ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)>,
    ) -> Result<(Stack<CurrentNetwork>, Vec<Operand<CurrentNetwork>>, Register<CurrentNetwork>)> {
        use crate::{Process, Program};

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
                input {r0} as {type_}.{mode};
                {opcode} {r0} into {r1};
                finalize {r0};
            finalize {function_name}:
                input {r0} as {type_}.public;
                {opcode} {r0} into {r1};
        "
        ))?;

        // Initialize the operands.
        let operands = vec![Operand::Register(r0)];

        // Initialize the stack.
        let stack = Stack::new(&Process::load_with_cache(cache)?, &program)?;

        Ok((stack, operands, r1))
    }

    fn check_hash<const VARIANT: u8>(
        operation: impl FnOnce(
            Vec<Operand<CurrentNetwork>>,
            Register<CurrentNetwork>,
        ) -> HashInstruction<CurrentNetwork, VARIANT>,
        opcode: Opcode,
        literal: &Literal<CurrentNetwork>,
        mode: &circuit::Mode,
        cache: &mut HashMap<String, (ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)>,
    ) {
        println!("Checking '{opcode}' for '{literal}.{mode}'");

        // Initialize the types.
        let type_ = literal.to_type();

        // Initialize the stack.
        let (stack, operands, destination) = sample_stack(opcode, type_, *mode, cache).unwrap();

        // Initialize the operation.
        let operation = operation(operands, destination.clone());
        // Initialize the function name.
        let function_name = Identifier::from_str("run").unwrap();
        // Initialize a destination operand.
        let destination_operand = Operand::Register(destination);

        // Attempt to evaluate the valid operand case.
        let mut evaluate_registers = sample_registers(&stack, &function_name, &[(literal, None)]).unwrap();
        let result_a = operation.evaluate(&stack, &mut evaluate_registers);

        // Attempt to execute the valid operand case.
        let mut execute_registers = sample_registers(&stack, &function_name, &[(literal, Some(*mode))]).unwrap();
        let result_b = operation.execute::<CurrentAleo>(&stack, &mut execute_registers);

        // Attempt to finalize the valid operand case.
        let mut finalize_registers = sample_finalize_registers(&stack, &function_name, &[literal]).unwrap();
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
        }

        // Reset the circuit.
        <CurrentAleo as circuit::Environment>::reset();
    }

    macro_rules! test_hash {
        ($name: tt, $hash:ident) => {
            paste::paste! {
                #[test]
                fn [<test _ $name _ is _ consistent>]() {
                    // Initialize the operation.
                    let operation = |operands, destination| $hash::<CurrentNetwork> { operands, destination };
                    // Initialize the opcode.
                    let opcode = $hash::<CurrentNetwork>::opcode();

                    // Prepare the rng.
                    let mut rng = TestRng::default();

                    // Prepare the test.
                    let modes = [circuit::Mode::Public, circuit::Mode::Private];

                    // Prepare the key cache.
                    let mut cache = Default::default();

                    for _ in 0..ITERATIONS {
                        let literals = crate::sample_literals!(CurrentNetwork, &mut rng);
                        for literal in literals.iter() {
                            for mode in modes.iter() {
                                check_hash(operation, opcode, literal, mode, &mut cache);
                            }
                        }
                    }
                }
            }
        };
    }

    test_hash!(hash_bhp256, HashBHP256);
    test_hash!(hash_bhp512, HashBHP512);
    test_hash!(hash_bhp768, HashBHP768);
    test_hash!(hash_bhp1024, HashBHP1024);
    test_hash!(hash_psd2, HashPSD2);
    test_hash!(hash_psd4, HashPSD4);
    test_hash!(hash_psd8, HashPSD8);

    // Note this test must be explicitly written, instead of using the macro, because HashPED64 fails on certain input types.
    #[test]
    fn test_hash_ped64_is_consistent() {
        // Initialize the operation.
        let operation = |operands, destination| HashPED64::<CurrentNetwork> { operands, destination };
        // Initialize the opcode.
        let opcode = HashPED64::<CurrentNetwork>::opcode();

        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let modes = [circuit::Mode::Public, circuit::Mode::Private];

        // Prepare the key cache.
        let mut cache = Default::default();

        for _ in 0..ITERATIONS {
            let literals = [
                Literal::Boolean(console::types::Boolean::rand(&mut rng)),
                Literal::I8(console::types::I8::rand(&mut rng)),
                Literal::I16(console::types::I16::rand(&mut rng)),
                Literal::I32(console::types::I32::rand(&mut rng)),
                Literal::U8(console::types::U8::rand(&mut rng)),
                Literal::U16(console::types::U16::rand(&mut rng)),
                Literal::U32(console::types::U32::rand(&mut rng)),
            ];
            for literal in literals.iter() {
                for mode in modes.iter() {
                    check_hash(operation, opcode, literal, mode, &mut cache);
                }
            }
        }
    }

    // Note this test must be explicitly written, instead of using the macro, because HashPED128 fails on certain input types.
    #[test]
    fn test_hash_ped128_is_consistent() {
        // Initialize the operation.
        let operation = |operands, destination| HashPED128::<CurrentNetwork> { operands, destination };
        // Initialize the opcode.
        let opcode = HashPED128::<CurrentNetwork>::opcode();

        // Prepare the rng.
        let mut rng = TestRng::default();

        // Prepare the test.
        let modes = [circuit::Mode::Public, circuit::Mode::Private];

        // Prepare the key cache.
        let mut cache = Default::default();

        for _ in 0..ITERATIONS {
            let literals = [
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
            for literal in literals.iter() {
                for mode in modes.iter() {
                    check_hash(operation, opcode, literal, mode, &mut cache);
                }
            }
        }
    }

    #[test]
    fn test_parse() {
        let (string, hash) = HashBHP512::<CurrentNetwork>::parse("hash.bhp512 r0 into r1").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(hash.operands.len(), 1, "The number of operands is incorrect");
        assert_eq!(hash.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(hash.destination, Register::Locator(1), "The destination register is incorrect");
    }
}
