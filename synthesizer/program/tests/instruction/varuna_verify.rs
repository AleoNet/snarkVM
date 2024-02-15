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

use crate::helpers::sample::{
    sample_assignment,
    sample_finalize_registers,
    sample_keys,
    sample_proof,
    sample_registers,
};

use circuit::{AleoV0, Eject, Mode};
use console::{
    network::MainnetV0,
    prelude::*,
    program::{ArrayType, Data, Identifier, Literal, LiteralType, Plaintext, PlaintextType, Register, Value, U32},
    types::Field,
};
use snarkvm_synthesizer_program::{
    FinalizeGlobalState,
    Opcode,
    Operand,
    Program,
    RegistersLoad,
    RegistersLoadCircuit,
    RegistersStore,
    VarunaVerify,
};
use synthesizer_process::{FinalizeRegisters, Process, Stack, StackProgramTypes};
use synthesizer_snark::{Proof, VerifyingKey};

type CurrentNetwork = MainnetV0;
type CurrentAleo = AleoV0;

const ITERATIONS: usize = 100;

/// Samples the stack. Note: Do not replicate this for real program use, it is insecure.
#[allow(clippy::type_complexity)]
fn sample_stack(
    proof_type: LiteralType<CurrentNetwork>,
    input_type: ArrayType<CurrentNetwork>,
) -> Result<(Stack<CurrentNetwork>, Vec<Operand<CurrentNetwork>>, Register<CurrentNetwork>)> {
    // Ensure that the proof type is a `Data` literal type.
    ensure!(matches!(proof_type, LiteralType::Data(_)), "The proof type must be a `Data` literal type");

    // Ensure that the input type is a two-dimensional array of field elements.
    let outer_element_type = match input_type.next_element_type() {
        PlaintextType::Array(array_type) => array_type,
        _ => bail!("Each input type must be a two dimensional array of field elements"),
    };
    let inner_element_type = outer_element_type.next_element_type();
    ensure!(
        matches!(inner_element_type, PlaintextType::Literal(LiteralType::Field)),
        "Each input type must be a two dimensional array of field elements"
    );

    // Initialize the program.
    let program = Program::from_str(&format!(
        "program testing.aleo;
            function test_varuna_verify:
                input r0 as {proof_type}.public;
                input r1 as $DATA[22u32].public;
                input r2 as {input_type}.public;
                input r3 as boolean.public;
                async test_varuna_verify r0 r1 r2 r3 into r4;
                output r4 as testing.aleo/test_varuna_verify.future;

            finalize test_varuna_verify:
                input r0 as {proof_type}.public;
                input r1 as $DATA[22u32].public;
                input r2 as {input_type}.public;
                input r3 as boolean.public;
                varuna.verify r0 r1 r2 into r4;
                assert.eq r4 r3;
        "
    ))?;

    // Initialize the operands.
    let proof_operand = Operand::Register(Register::Locator(0));
    let vk_operand = Operand::Register(Register::Locator(1));
    let input_operand = Operand::Register(Register::Locator(2));
    let operands = vec![proof_operand, vk_operand, input_operand];

    // Initialize the stack.
    let stack = Stack::new(&Process::load()?, &program)?;

    Ok((stack, operands, Register::Locator(4)))
}

fn check_varuna_verify(
    proof: Proof<CurrentNetwork>,
    vk: VerifyingKey<CurrentNetwork>,
    inputs: Vec<Vec<<CurrentNetwork as Environment>::Field>>,
    expected: bool,
) -> Result<()> {
    println!(
        "Checking 'varuna.verify' for {} instances and is expected to {}",
        inputs.len(),
        if expected { "succeed" } else { "fail" }
    );

    // Check that the inputs are at most 32 by 32.
    ensure!(inputs.len() <= 32, "The number of inputs must be at most 32");
    ensure!(
        inputs.iter().all(|input| input.len() <= 32),
        "The number of field elements in each input must be at most 32"
    );

    // Check that all input in the inputs are of the same length.
    ensure!(inputs.iter().all(|input| input.len() == inputs[0].len()), "All inputs must be of the same length");

    // Initialize the types.
    let data = Data::encode_from_bytes_le(&proof.to_bytes_le()?)?;
    let proof_type = LiteralType::Data(U32::new(data.len() as u32));

    let input_type = ArrayType::new(PlaintextType::Literal(LiteralType::Field), vec![
        U32::new(inputs.len() as u32),
        U32::new(inputs[0].len() as u32),
    ])?;

    // Initialize the stack.
    let (stack, operands, destination) = sample_stack(proof_type, input_type)?;

    // Initialize the function name.
    let function_name = Identifier::from_str("test_varuna_verify")?;

    // Initialize the instruction.
    let instruction = VarunaVerify::new(operands, destination)?;

    // Construct the finalize registers.
    let mut finalize_registers = FinalizeRegisters::<CurrentNetwork>::new(
        FinalizeGlobalState::from(1, 1, [0; 32]),
        <CurrentNetwork as Network>::TransitionID::default(),
        function_name,
        stack.get_finalize_types(&function_name)?.clone(),
    );

    // Add the proof to the 0-th register.
    finalize_registers.store(&stack, &Register::Locator(0), Value::Plaintext(Plaintext::from(Literal::Data(data))))?;

    // Add the verifying key to the 1-th register.
    let data = Data::encode_from_bytes_le(&vk.to_bytes_le()?)?;
    finalize_registers.store(&stack, &Register::Locator(1), Value::Plaintext(Plaintext::from(Literal::Data(data))))?;

    // Add the inputs to the 2-th register.
    let outer = inputs
        .into_iter()
        .map(|input| {
            let inner = input.into_iter().map(|field| Plaintext::from(Literal::Field(Field::new(field)))).collect();
            Plaintext::Array(inner, Default::default())
        })
        .collect();
    let inputs = Plaintext::Array(outer, Default::default());
    finalize_registers.store(&stack, &Register::Locator(2), Value::Plaintext(inputs))?;

    // Attempt to finalize.
    let result = instruction.finalize(&stack, &mut finalize_registers);

    // Check that the result is as expected.
    ensure!(result.is_ok() == expected);

    Ok(())
}

#[test]
fn test_varuna_verify() {
    // Sample a proof.
    let proof = sample_proof();

    // Sample the verifying key.
    let (_, verifying_key) = sample_keys();

    // Sample the public inputs.
    let assignment = vec![sample_assignment().public_inputs().iter().map(|(_, field)| *field).collect_vec()];

    // Check that varuna.verify succeeds for the sample proof and verifying key.
    check_varuna_verify(proof, verifying_key, assignment, true).unwrap();
}
