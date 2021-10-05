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

use crate::prelude::*;
use snarkvm_algorithms::prelude::*;
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::ToMinimalBits;

use rand::SeedableRng;
use rand_chacha::ChaChaRng;

fn dpc_execute_circuits_test<N: Network>(expected_inner_num_constraints: usize, expected_outer_num_constraints: usize) {
    let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

    let recipient = Account::new(&mut rng).unwrap();
    let amount = AleoAmount::from_bytes(10);
    let state = StateTransition::builder()
        .add_output(Output::new(recipient.address, amount, Payload::default(), None).unwrap())
        .add_output(Output::new(recipient.address, amount, Payload::default(), None).unwrap())
        .build(&mut rng)
        .unwrap();

    let authorization = DPC::<N>::authorize(&vec![], &state, &mut rng).unwrap();
    let transaction_id = authorization.to_transaction_id().unwrap();

    // Execute the program circuit.
    let execution = state
        .executable()
        .execute(PublicVariables::new(transaction_id))
        .unwrap();

    // Compute the encrypted records.
    let (_encrypted_records, encrypted_record_hashes, encrypted_record_randomizers) =
        authorization.to_encrypted_records(&mut rng).unwrap();

    let TransactionAuthorization {
        kernel,
        input_records,
        output_records,
        signatures,
    } = authorization;

    // Construct the ledger witnesses.
    let ledger_proof = LedgerProof::<N>::default();

    //////////////////////////////////////////////////////////////////////////

    // Construct the inner circuit public and private variables.
    let inner_public_variables = InnerPublicVariables::new(
        transaction_id,
        ledger_proof.block_hash(),
        &encrypted_record_hashes,
        Some(state.executable().program_id()),
    )
    .unwrap();
    let inner_private_variables = InnerPrivateVariables::new(
        &kernel,
        input_records.clone(),
        ledger_proof,
        signatures,
        output_records.clone(),
        encrypted_record_randomizers,
        state.executable(),
    )
    .unwrap();

    // Check that the core check constraint system was satisfied.
    let mut inner_cs = TestConstraintSystem::<N::InnerScalarField>::new();

    let inner_circuit = InnerCircuit::new(inner_public_variables.clone(), inner_private_variables);
    inner_circuit
        .generate_constraints(&mut inner_cs.ns(|| "Inner circuit"))
        .unwrap();

    let candidate_inner_num_constraints = inner_cs.num_constraints();

    if !inner_cs.is_satisfied() {
        println!("=========================================================");
        println!("Outer circuit num constraints: {}", candidate_inner_num_constraints);
        println!("Unsatisfied constraints:\n{}", inner_cs.which_is_unsatisfied().unwrap());
        println!("=========================================================");
    }

    println!("=========================================================");
    println!("Inner circuit num constraints: {}", candidate_inner_num_constraints);
    assert_eq!(expected_inner_num_constraints, candidate_inner_num_constraints);
    println!("=========================================================");

    assert!(inner_cs.is_satisfied());

    // Generate inner snark parameters and proof for verification in the outer snark
    let (inner_proving_key, inner_verifying_key) =
        <N as Network>::InnerSNARK::setup(&InnerCircuit::<N>::blank(), &mut SRS::CircuitSpecific(&mut rng)).unwrap();

    // NOTE: Do not change this to `N::inner_circuit_id()` as that will load the *saved* inner circuit VK.
    let inner_circuit_id = <N as Network>::inner_circuit_id_crh()
        .hash_bits(&inner_verifying_key.to_minimal_bits())
        .unwrap();

    let inner_proof = <N as Network>::InnerSNARK::prove(&inner_proving_key, &inner_circuit, &mut rng).unwrap();

    // Verify that the inner circuit proof passes.
    assert!(<N as Network>::InnerSNARK::verify(&inner_verifying_key, &inner_public_variables, &inner_proof).unwrap());

    // Construct the outer circuit public and private variables.
    let outer_public_variables = OuterPublicVariables::new(&inner_public_variables, inner_circuit_id);
    let outer_private_variables = OuterPrivateVariables::new(inner_verifying_key, inner_proof, execution);

    // Check that the proof check constraint system was satisfied.
    let mut outer_cs = TestConstraintSystem::<N::OuterScalarField>::new();

    execute_outer_circuit::<N, _>(
        &mut outer_cs.ns(|| "Outer circuit"),
        &outer_public_variables,
        &outer_private_variables,
    )
    .unwrap();

    let candidate_outer_num_constraints = outer_cs.num_constraints();

    if !outer_cs.is_satisfied() {
        println!("=========================================================");
        println!("Outer circuit num constraints: {}", candidate_outer_num_constraints);
        println!("Unsatisfied constraints:\n{}", outer_cs.which_is_unsatisfied().unwrap());
        println!("=========================================================");
    }

    println!("=========================================================");
    println!("Outer circuit num constraints: {}", candidate_outer_num_constraints);
    assert_eq!(expected_outer_num_constraints, candidate_outer_num_constraints);
    println!("=========================================================");

    assert!(outer_cs.is_satisfied());
}

mod testnet1 {
    use super::*;
    use crate::testnet1::*;

    #[test]
    fn test_dpc_execute_circuits() {
        dpc_execute_circuits_test::<Testnet1>(223411, 161057);
    }
}

mod testnet2 {
    use super::*;
    use crate::testnet2::*;

    #[test]
    fn test_dpc_execute_circuits() {
        dpc_execute_circuits_test::<Testnet2>(223411, 253185);
    }
}
