// Copyright (C) 2019-2021 Aleo Systems Inc.
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
use snarkvm_utilities::ToBytes;

use rand::thread_rng;

fn dpc_execute_circuits_test<N: Network>(expected_inner_num_constraints: usize) {
    let rng = &mut thread_rng();

    let recipient = Account::new(rng);
    let amount = AleoAmount::from_gate(10);
    let request = Request::new_coinbase(recipient.address(), amount, false, rng).unwrap();
    let response = ResponseBuilder::new()
        .add_request(request.clone())
        .add_output(Output::new(recipient.address(), amount, Default::default(), None).unwrap())
        .build(rng)
        .unwrap();

    //////////////////////////////////////////////////////////////////////////

    // Fetch the ledger root, serial numbers, and program ID.
    let ledger_root = LedgerTree::<N>::new().unwrap().root();
    let serial_numbers = request.to_serial_numbers().unwrap();
    let program_id = request.to_program_id().unwrap();

    // Fetch the commitments and ciphertexts.
    let commitments = response.commitments();

    // Compute the value balance.
    let mut value_balance = AleoAmount::ZERO;
    for record in request.records().iter().take(N::NUM_INPUT_RECORDS) {
        value_balance = value_balance.add(record.value());
    }
    for record in response.records().iter().take(N::NUM_OUTPUT_RECORDS) {
        value_balance = value_balance.sub(record.value());
    }

    // Compute the local transitions root.
    let local_transitions_root = Transitions::<N>::new().unwrap().root();

    // Compute the transition ID.
    let transition_id = Transition::<N>::compute_transition_id(&serial_numbers, &commitments).unwrap();

    //////////////////////////////////////////////////////////////////////////

    // Construct the inner circuit public and private variables.
    let inner_public =
        InnerPublicVariables::new(transition_id, value_balance, ledger_root, local_transitions_root, Some(program_id));
    let inner_private = InnerPrivateVariables::new(&request, &response).unwrap();

    // Check that the core check constraint system was satisfied.
    let mut inner_cs = TestConstraintSystem::<N::InnerScalarField>::new();

    let inner_circuit = InnerCircuit::new(inner_public, inner_private);
    inner_circuit.generate_constraints(&mut inner_cs.ns(|| "Inner circuit")).unwrap();

    let candidate_inner_num_constraints = inner_cs.num_constraints();
    let (num_non_zero_a, num_non_zero_b, num_non_zero_c) = inner_cs.num_non_zero();

    if !inner_cs.is_satisfied() {
        println!("=========================================================");
        println!("Inner circuit num constraints: {}", candidate_inner_num_constraints);
        println!("Unsatisfied constraints:\n{}", inner_cs.which_is_unsatisfied().unwrap());
        println!("=========================================================");
    }

    println!("=========================================================");
    println!("Inner circuit num constraints: {}", candidate_inner_num_constraints);
    assert_eq!(expected_inner_num_constraints, candidate_inner_num_constraints);
    println!("=========================================================");

    println!("=========================================================");
    println!("Inner circuit num non_zero_a: {}", num_non_zero_a);
    println!("Inner circuit num non_zero_b: {}", num_non_zero_b);
    println!("Inner circuit num non_zero_c: {}", num_non_zero_c);
    println!("=========================================================");

    assert!(inner_cs.is_satisfied());

    //////////////////////////////////////////////////////////////////////////

    // Generate inner circuit parameters and proof for verification in the outer circuit.
    let (inner_proving_key, inner_verifying_key) =
        <N as Network>::InnerSNARK::setup(&InnerCircuit::<N>::blank(), &mut SRS::CircuitSpecific(rng)).unwrap();

    // // NOTE: Do not change this to `N::inner_circuit_id()` as that will load the *saved* inner circuit VK.
    // let inner_circuit_id: N::InnerCircuitID = <N as Network>::inner_circuit_id_crh()
    //     .hash_bits(&inner_verifying_key.to_minimal_bits())
    //     .unwrap()
    //     .into();

    let inner_proof = <N as Network>::InnerSNARK::prove(&inner_proving_key, &inner_circuit, rng).unwrap();
    assert_eq!(N::INNER_PROOF_SIZE_IN_BYTES, inner_proof.to_bytes_le().unwrap().len());

    // Verify that the inner circuit proof passes.
    assert!(<N as Network>::InnerSNARK::verify(&inner_verifying_key, &inner_public, &inner_proof).unwrap());

    //////////////////////////////////////////////////////////////////////////

    // Compute the noop execution.
    let execution = Execution::<N>::from(
        *N::noop_program_id(),
        N::noop_program_path().clone(),
        N::noop_circuit_verifying_key().clone(),
        Noop::<N>::new()
            .execute(ProgramPublicVariables::new(transition_id), &NoopPrivateVariables::<N>::new_blank().unwrap())
            .unwrap(),
        inner_proof.into(),
    )
    .unwrap();
    assert_eq!(N::PROGRAM_PROOF_SIZE_IN_BYTES, N::ProgramProof::to_bytes_le(&execution.program_proof).unwrap().len());

    // Verify that the program proof passes.
    assert!(execution.verify(&inner_verifying_key, transition_id, value_balance, ledger_root, local_transitions_root,));
}

mod testnet1 {
    use super::*;
    use crate::testnet1::*;

    #[test]
    fn test_dpc_execute_circuits() {
        dpc_execute_circuits_test::<Testnet1>(253822);
    }
}

mod testnet2 {
    use super::*;
    use crate::testnet2::*;

    #[test]
    fn test_dpc_execute_circuits() {
        dpc_execute_circuits_test::<Testnet2>(253822);
    }
}
