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

use crate::helpers::sample::{sample_assignment, sample_keys};

use console::{
    network::MainnetV0,
    prelude::*,
    program::{ArrayType, Data, Identifier, Literal, LiteralType, Plaintext, PlaintextType, Register, Value, U32},
    types::Field,
};
use snarkvm_synthesizer_program::{FinalizeGlobalState, Operand, Program, RegistersLoad, RegistersStore, VarunaVerify};
use synthesizer_process::{FinalizeRegisters, Process, Stack, StackProgramTypes};
use synthesizer_snark::{Proof, ProvingKey, VerifyingKey};

type CurrentNetwork = MainnetV0;

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
    proof: &Proof<CurrentNetwork>,
    vk: &VerifyingKey<CurrentNetwork>,
    inputs: &Vec<Vec<<CurrentNetwork as Environment>::Field>>,
) -> Result<bool> {
    println!("Checking 'varuna.verify' for {} instances", inputs.len(),);

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
        .iter()
        .map(|input| {
            let inner = input.iter().map(|field| Plaintext::from(Literal::Field(Field::new(*field)))).collect();
            Plaintext::Array(inner, Default::default())
        })
        .collect();
    let inputs = Plaintext::Array(outer, Default::default());
    finalize_registers.store(&stack, &Register::Locator(2), Value::Plaintext(inputs))?;

    // Attempt to finalize.
    instruction.finalize(&stack, &mut finalize_registers).unwrap();

    // Get the result from the destination register.
    let result = match finalize_registers.load(&stack, &Operand::Register(Register::Locator(4)))? {
        Value::Plaintext(Plaintext::Literal(Literal::Boolean(result), _)) => *result,
        _ => bail!("The result must be a boolean"),
    };

    Ok(result)
}

#[test]
fn test_single_instance_varuna_verify() {
    // Sample an RNG.
    let rng = &mut TestRng::default();

    // Sample the first set of keys.
    let (first_proving_key, first_verifying_key) = sample_keys(&[5]).pop().unwrap();

    // Sample the first assignment.
    let first_assignment = sample_assignment(Field::from_u64(2), 5);

    // Get the first set of public inputs.
    let first_inputs = vec![first_assignment.public_inputs().iter().map(|(_, field)| *field).collect_vec()];

    // Generate the first proof.
    let first_proof = first_proving_key.prove("test_varuna_verify", &first_assignment, rng).unwrap();

    // Sample the second set of keys.
    let (second_proving_key, second_verifying_key) = sample_keys(&[10]).pop().unwrap();

    // Sample the second assignment.
    let second_assignment = sample_assignment(Field::from_u64(3), 10);

    // Get the second set of public inputs.
    let second_inputs = vec![second_assignment.public_inputs().iter().map(|(_, field)| *field).collect_vec()];

    // Generate the second proof.
    let second_proof = second_proving_key.prove("test_varuna_verify", &second_assignment, rng).unwrap();

    // For these circuits,
    //  - check that the proofs are different.
    //  - check that the verifying keys are different.
    //  - check that the first and second verifier inputs are the same.
    // This is the case for this particular circuit.
    assert_ne!(first_proof, second_proof);
    assert_ne!(first_verifying_key, second_verifying_key);
    assert_eq!(first_inputs, second_inputs);

    // Check that varuna.verify succeeds for appropriate combinations of proofs and verifying keys.
    assert!(check_varuna_verify(&first_proof, &first_verifying_key, &first_inputs).unwrap());
    assert!(check_varuna_verify(&second_proof, &second_verifying_key, &second_inputs).unwrap());
    assert!(check_varuna_verify(&first_proof, &first_verifying_key, &first_inputs).unwrap());
    assert!(check_varuna_verify(&second_proof, &second_verifying_key, &first_inputs).unwrap());

    // Check that the varuna.verify fails for improper combinations of proofs and verifying keys.
    assert!(!check_varuna_verify(&first_proof, &second_verifying_key, &first_inputs).unwrap());
    assert!(!check_varuna_verify(&first_proof, &second_verifying_key, &second_inputs).unwrap());
    assert!(!check_varuna_verify(&second_proof, &first_verifying_key, &second_inputs).unwrap());
    assert!(!check_varuna_verify(&second_proof, &first_verifying_key, &first_inputs).unwrap());
}

#[test]
fn test_maximum_instances_varuna_verify() {
    // Sample the keys.
    let (proving_key, verifying_key) = sample_keys(&[10]).pop().unwrap();

    // Sample 32 valid assignments.
    let assignments = (0..32).map(|i| sample_assignment(Field::from_u64(i), 10)).collect_vec();

    // Extract the public inputs.
    let inputs = assignments
        .iter()
        .map(|assignment| assignment.public_inputs().iter().map(|(_, field)| *field).collect_vec())
        .collect_vec();

    // Batch prove the assignments.
    let proof =
        ProvingKey::prove_batch("test_varuna_verify", &[(proving_key.clone(), assignments)], &mut TestRng::default())
            .unwrap();

    // Check that varuna.verify succeeds for the sample proof and verifying key.
    assert!(check_varuna_verify(&proof, &verifying_key, &inputs).unwrap());

    // Sample 33 assignments.
    let assignments = (0..33).map(|i| sample_assignment(Field::from_u64(i), 10)).collect_vec();

    // Extract the public inputs.
    let inputs = assignments
        .iter()
        .map(|assignment| assignment.public_inputs().iter().map(|(_, field)| *field).collect_vec())
        .collect_vec();

    // Batch prove the assignments.
    let proof =
        ProvingKey::prove_batch("test_varuna_verify", &[(proving_key, assignments)], &mut TestRng::default()).unwrap();

    // Check that varuna.verify fails for the sample proof and verifying key.
    // Note: The maximum number of instances is 32 because the maximum length of an array is bounded to 32.
    let result = check_varuna_verify(&proof, &verifying_key, &inputs);
    assert!(result.is_err());
}

// TODO (@d0cd). Test multiple different circuits.
