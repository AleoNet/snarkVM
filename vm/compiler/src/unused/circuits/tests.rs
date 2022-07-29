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

use crate::{circuits::*, prelude::*};
use snarkvm_algorithms::prelude::*;
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, TestConstraintSystem};

use itertools::Itertools;
use rand::thread_rng;

fn dpc_execute_circuits_test<N: Network>(
    expected_input_num_constraints: usize,
    expected_output_num_constraints: usize,
    num_inputs: usize,
    num_outputs: usize,
) {
    let rng = &mut thread_rng();

    let sender = Account::new(rng);
    let recipient = Account::new(rng);
    let amount = AleoAmount::from_gate(0);

    let mut records = Vec::new();
    let mut ledger_proofs = Vec::new();
    for _ in 0..num_inputs {
        let record = Record::new_noop(sender.address(), rng).unwrap();
        let ledger_proof = LedgerProof::default();

        records.push(record.clone());
        ledger_proofs.push(ledger_proof);
    }

    // Coinbase transactions do not have input proofs, so we use a dummy transfer to test both
    // the input and output circuits.
    let request: Request<N> =
        Request::new_transfer(sender.private_key(), records, ledger_proofs, recipient.address(), amount, false, rng)
            .unwrap();

    let mut response_builder = ResponseBuilder::new().add_request(request.clone());

    for _ in 0..num_outputs {
        response_builder = response_builder.add_output(Output::new(recipient.address(), amount, None, None).unwrap());
    }

    let response: Response<N> = response_builder.build(rng).unwrap();

    //////////////////////////////////////////////////////////////////////////

    // Fetch the ledger root, serial numbers, and program ID.
    let ledger_root = LedgerTree::<N>::new().unwrap().root();
    let serial_numbers = request.to_serial_numbers().unwrap();
    let program_id = request.to_program_id().unwrap();

    // Fetch the commitments and ciphertexts.
    let commitments = response.commitments();

    // Compute the value balance.
    let mut value_balance = AleoAmount::ZERO;
    for record in request.records().iter() {
        value_balance = value_balance.add(record.value());
    }
    for record in response.records().iter() {
        value_balance = value_balance.sub(record.value());
    }

    // Compute the local transitions root.
    let local_transitions_root = Transitions::<N>::new().unwrap().root();

    // Compute the transition ID.
    let transition_id = Transition::<N>::compute_transition_id(&serial_numbers, &commitments).unwrap();

    //////////////////////////////////////////////////////////////////////////

    // Generate input circuit parameters and proof.
    let (input_proving_key, input_verifying_key) =
        <N as Network>::InputSNARK::setup(&InputCircuit::<N>::blank(), &mut SRS::CircuitSpecific(rng)).unwrap();

    let mut input_circuits = Vec::new();
    let mut input_public_inputs = Vec::new();

    // Compute the input circuit proofs.
    for (
        ((((record, serial_number), ledger_proof), signature), input_value_commitment),
        input_value_commitment_randomness,
    ) in request
        .records()
        .iter()
        .zip_eq(request.to_serial_numbers().unwrap().iter())
        .zip_eq(request.ledger_proofs())
        .zip_eq(request.signatures())
        .zip_eq(response.input_value_commitments())
        .zip_eq(response.input_value_commitment_randomness())
    {
        // Check that the input constraint system was satisfied.
        let mut input_cs = TestConstraintSystem::<N::InnerScalarField>::new();

        let input_public = InputPublicVariables::<N>::new(
            *serial_number,
            input_value_commitment.clone(),
            ledger_root,
            local_transitions_root,
            program_id,
        );
        let input_private = InputPrivateVariables::<N>::new(
            record.clone(),
            ledger_proof.clone(),
            signature.clone(),
            *input_value_commitment_randomness,
        )
        .unwrap();

        let input_circuit = InputCircuit::<N>::new(input_public.clone(), input_private);
        input_circuit.generate_constraints(&mut input_cs.ns(|| "Input circuit")).unwrap();

        let candidate_input_num_constraints = input_cs.num_constraints();
        let (num_non_zero_a, num_non_zero_b, num_non_zero_c) = input_cs.num_non_zero();

        if !dbg!(input_cs.is_satisfied()) {
            println!("=========================================================");
            println!("Input circuit num constraints: {}", candidate_input_num_constraints);
            println!("Unsatisfied constraints:\n{}", input_cs.which_is_unsatisfied().unwrap());
            println!("=========================================================");
        }

        println!("=========================================================");
        println!("Input circuit num constraints: {}", candidate_input_num_constraints);
        assert_eq!(expected_input_num_constraints, candidate_input_num_constraints);
        println!("=========================================================");

        println!("=========================================================");
        println!("Input circuit num non_zero_a: {}", num_non_zero_a);
        println!("Input circuit num non_zero_b: {}", num_non_zero_b);
        println!("Input circuit num non_zero_c: {}", num_non_zero_c);
        println!("=========================================================");

        assert!(input_cs.is_satisfied());

        //////////////////////////////////////////////////////////////////////////

        input_circuits.push(input_circuit);
        input_public_inputs.push(input_public);

        //////////////////////////////////////////////////////////////////////////
    }
    let proving_start = std::time::Instant::now();
    let input_proof = <N as Network>::InputSNARK::prove_batch(&input_proving_key, &input_circuits, rng).unwrap();
    println!("Proving time for {num_inputs} x {num_outputs}: {}", proving_start.elapsed().as_secs_f64());

    let verifying_start = std::time::Instant::now();
    // Verify that the inner circuit proof passes.
    assert!(
        <N as Network>::InputSNARK::verify_batch(&input_verifying_key, &input_public_inputs, &input_proof).unwrap()
    );
    println!("Verifying time: {}", verifying_start.elapsed().as_secs_f64());

    //////////////////////////////////////////////////////////////////////////

    // Generate output circuit parameters and proof.
    let (output_proving_key, output_verifying_key) =
        <N as Network>::OutputSNARK::setup(&OutputCircuit::<N>::blank(), &mut SRS::CircuitSpecific(rng)).unwrap();

    let mut output_circuits = Vec::new();
    let mut output_public_inputs = Vec::new();

    // Compute the output circuit proofs.
    for (
        (((record, commitment), encryption_randomness), output_value_commitment),
        output_value_commitment_randomness,
    ) in response
        .records()
        .iter()
        .zip_eq(response.commitments())
        .zip_eq(response.encryption_randomness())
        .zip_eq(response.output_value_commitments())
        .zip_eq(response.output_value_commitment_randomness())
    {
        // Check that the output constraint system was satisfied.
        let mut output_cs = TestConstraintSystem::<N::InnerScalarField>::new();

        let output_public = OutputPublicVariables::<N>::new(commitment, output_value_commitment.clone(), program_id);
        let output_private = OutputPrivateVariables::<N>::new(
            record.clone(),
            *encryption_randomness,
            *output_value_commitment_randomness,
        )
        .unwrap();

        let output_circuit = OutputCircuit::<N>::new(output_public.clone(), output_private);
        output_circuit.generate_constraints(&mut output_cs.ns(|| "Output circuit")).unwrap();

        let candidate_output_num_constraints = output_cs.num_constraints();
        let (num_non_zero_a, num_non_zero_b, num_non_zero_c) = output_cs.num_non_zero();

        if !dbg!(output_cs.is_satisfied()) {
            println!("=========================================================");
            println!("Output circuit num constraints: {}", candidate_output_num_constraints);
            println!("Unsatisfied constraints:\n{}", output_cs.which_is_unsatisfied().unwrap());
            println!("=========================================================");
        }

        println!("=========================================================");
        println!("Output circuit num constraints: {}", candidate_output_num_constraints);
        assert_eq!(expected_output_num_constraints, candidate_output_num_constraints);
        println!("=========================================================");

        println!("=========================================================");
        println!("Output circuit num non_zero_a: {}", num_non_zero_a);
        println!("Output circuit num non_zero_b: {}", num_non_zero_b);
        println!("Output circuit num non_zero_c: {}", num_non_zero_c);
        println!("=========================================================");

        assert!(output_cs.is_satisfied());

        //////////////////////////////////////////////////////////////////////////

        output_circuits.push(output_circuit);
        output_public_inputs.push(output_public);
    }
    let proving_start = std::time::Instant::now();
    let output_proof = <N as Network>::OutputSNARK::prove_batch(&output_proving_key, &output_circuits, rng).unwrap();
    println!("Proving time for {num_inputs} x {num_outputs}: {}", proving_start.elapsed().as_secs_f64());

    let verifying_start = std::time::Instant::now();
    // Verify that the inner circuit proof passes.
    assert!(
        <N as Network>::OutputSNARK::verify_batch(&output_verifying_key, &output_public_inputs, &output_proof).unwrap()
    );
    println!("Verifying time: {}", verifying_start.elapsed().as_secs_f64());

    //////////////////////////////////////////////////////////////////////////

    // Construct the execution.
    let execution = Execution::<N>::from(None).unwrap();

    // Verify that the program proof passes.
    assert!(execution.verify(transition_id));
}

mod testnet1 {
    use super::*;
    use crate::testnet1::*;

    const EXPECTED_INPUT_NUM_CONSTRAINTS: usize = 112285;
    const EXPECTED_OUTPUT_NUM_CONSTRAINTS: usize = 18731;

    #[test]
    fn test_dpc_execute_circuits() {
        dpc_execute_circuits_test::<Testnet1>(EXPECTED_INPUT_NUM_CONSTRAINTS, EXPECTED_OUTPUT_NUM_CONSTRAINTS, 1, 1);
    }

    // TODO (raychu86): Move these tests upstream to the VM when variable size output transfers are supported.
    #[test]
    fn test_dpc_execute_circuits_variable_inputs_and_outputs() {
        dpc_execute_circuits_test::<Testnet1>(EXPECTED_INPUT_NUM_CONSTRAINTS, EXPECTED_OUTPUT_NUM_CONSTRAINTS, 2, 2);
        dpc_execute_circuits_test::<Testnet1>(EXPECTED_INPUT_NUM_CONSTRAINTS, EXPECTED_OUTPUT_NUM_CONSTRAINTS, 4, 4);
    }

    #[test]
    fn test_dpc_execute_circuits_variable_inputs_and_outputs_large() {
        dpc_execute_circuits_test::<Testnet1>(EXPECTED_INPUT_NUM_CONSTRAINTS, EXPECTED_OUTPUT_NUM_CONSTRAINTS, 1, 8);
        dpc_execute_circuits_test::<Testnet1>(EXPECTED_INPUT_NUM_CONSTRAINTS, EXPECTED_OUTPUT_NUM_CONSTRAINTS, 8, 1);
    }
}

mod testnet2 {
    use super::*;
    use crate::testnet2::*;

    const EXPECTED_INPUT_NUM_CONSTRAINTS: usize = 112285;
    const EXPECTED_OUTPUT_NUM_CONSTRAINTS: usize = 18731;

    #[test]
    fn test_dpc_execute_circuits() {
        dpc_execute_circuits_test::<Testnet2>(EXPECTED_INPUT_NUM_CONSTRAINTS, EXPECTED_OUTPUT_NUM_CONSTRAINTS, 1, 1);
    }

    #[test]
    fn test_dpc_execute_circuits_variable_inputs_and_outputs() {
        dpc_execute_circuits_test::<Testnet2>(EXPECTED_INPUT_NUM_CONSTRAINTS, EXPECTED_OUTPUT_NUM_CONSTRAINTS, 2, 2);
        dpc_execute_circuits_test::<Testnet2>(EXPECTED_INPUT_NUM_CONSTRAINTS, EXPECTED_OUTPUT_NUM_CONSTRAINTS, 4, 4);
    }

    #[test]
    fn test_dpc_execute_circuits_variable_inputs_and_outputs_large() {
        dpc_execute_circuits_test::<Testnet2>(EXPECTED_INPUT_NUM_CONSTRAINTS, EXPECTED_OUTPUT_NUM_CONSTRAINTS, 1, 8);
        dpc_execute_circuits_test::<Testnet2>(EXPECTED_INPUT_NUM_CONSTRAINTS, EXPECTED_OUTPUT_NUM_CONSTRAINTS, 8, 1);
    }
}
