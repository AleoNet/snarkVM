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

use snarkvm_algorithms::prelude::*;
use snarkvm_curves::bls12_377::{Fq, Fr};
use snarkvm_dpc::{prelude::*, testnet2::*};
use snarkvm_ledger::{ledger::*, prelude::*};
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::{FromBytes, ToBytes, ToMinimalBits};

use rand::SeedableRng;
use rand_chacha::ChaChaRng;

#[test]
fn test_testnet2_inner_circuit_id_sanity_check() {
    let expected_inner_circuit_id = vec![
        126, 111, 139, 25, 71, 200, 187, 91, 53, 148, 135, 104, 35, 224, 153, 158, 31, 65, 204, 37, 107, 242, 142, 41,
        226, 82, 131, 66, 67, 140, 190, 114, 171, 251, 252, 230, 249, 206, 124, 159, 3, 72, 126, 95, 197, 250, 48, 0,
    ];
    let candidate_inner_circuit_id = <Testnet2 as Network>::inner_circuit_id().to_bytes_le().unwrap();
    assert_eq!(expected_inner_circuit_id, candidate_inner_circuit_id);
}

#[test]
fn dpc_testnet2_integration_test() {
    let mut rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

    // Create a genesis block.
    let recipient = Account::new(rng).unwrap();
    let genesis_block = Block::<Testnet2>::new_genesis(recipient.address(), rng).unwrap();
    let coinbase_transaction = genesis_block.to_coinbase_transaction().unwrap();

    let ledger = Ledger::<Testnet2, MemDb>::new(None, genesis_block).unwrap();

    // Check that the coinbase transaction is serialized and deserialized correctly.
    let transaction_bytes = coinbase_transaction.to_bytes_le().unwrap();
    let recovered_transaction = Transaction::<Testnet2>::read_le(&transaction_bytes[..]).unwrap();
    assert_eq!(coinbase_transaction, recovered_transaction);

    // Check that coinbase record can be decrypted from the transaction.
    let encrypted_record = &coinbase_transaction.encrypted_records()[0];
    let view_key = ViewKey::from_private_key(recipient.private_key()).unwrap();
    let decrypted_record = encrypted_record.decrypt(&view_key).unwrap();
    assert_eq!(decrypted_record.owner(), recipient.address());
    assert_eq!(decrypted_record.value() as i64, Block::<Testnet2>::block_reward(0).0);

    // Construct the previous block hash and new block height.
    let previous_block = ledger.latest_block().unwrap();
    let previous_hash = previous_block.to_block_hash().unwrap();
    let block_height = previous_block.header.height() + 1;
    assert_eq!(block_height, 1);

    // Construct the new block transactions.
    let amount = Block::<Testnet2>::block_reward(block_height);
    let transaction = Transaction::<Testnet2>::new_coinbase(recipient.address(), amount, rng).unwrap();
    let transactions = Transactions::from(&[transaction]).unwrap();
    let transactions_root = transactions.to_transactions_root().unwrap();

    // Construct the new serial numbers root.
    let transaction_serial_numbers = transactions.to_serial_numbers().unwrap();
    let new_serial_numbers_tree = ledger.build_new_serial_number_tree(transaction_serial_numbers).unwrap();
    let serial_numbers_root = *new_serial_numbers_tree.root();

    // Construct the new commitments root.
    let transaction_commitments = transactions.to_commitments().unwrap();
    let new_commitments_tree = ledger.build_new_commitment_tree(transaction_commitments).unwrap();
    let commitments_root = *new_commitments_tree.root();

    // Construct the new block header.
    let header = BlockHeader::new(
        block_height,
        previous_block.header.difficulty_target(),
        transactions_root,
        serial_numbers_root,
        commitments_root,
        &mut rng,
    )
    .unwrap();

    // Construct the new block.
    let block = Block {
        previous_hash,
        header,
        transactions,
    };

    ledger.insert_and_commit(&block).unwrap();
    assert_eq!(ledger.block_height(), 1);
}

#[test]
fn test_testnet2_dpc_execute_constraints() {
    let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

    let recipient = Account::new(&mut rng).unwrap();
    let amount = AleoAmount::from_bytes(10 as i64);
    let state = StateTransition::builder()
        .add_output(Output::new(recipient.address, amount, Payload::default(), None).unwrap())
        .add_output(Output::new(recipient.address, amount, Payload::default(), None).unwrap())
        .build(&mut rng)
        .unwrap();

    let authorization = DPC::<Testnet2>::authorize(&vec![], &state, &mut rng).unwrap();

    // Generate the local data.
    let local_data = authorization.to_local_data(&mut rng).unwrap();

    // Execute the program circuit.
    let execution = state
        .executable()
        .execute(PublicVariables::new(local_data.root()))
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

    let local_data_root = local_data.root();

    // Construct the ledger witnesses.
    let ledger_proof = LedgerProof::<Testnet2>::default();
    let ledger_digest = ledger_proof.commitments_root();
    let input_witnesses = ledger_proof.commitment_inclusion_proofs();

    //////////////////////////////////////////////////////////////////////////

    // Construct the inner circuit public and private variables.
    let inner_public_variables = InnerPublicVariables::new(
        &kernel,
        &ledger_digest,
        &encrypted_record_hashes,
        Some(state.executable().program_id()),
        Some(local_data.root().clone()),
    )
    .unwrap();
    let inner_private_variables = InnerPrivateVariables::new(
        input_records.clone(),
        input_witnesses,
        signatures,
        output_records.clone(),
        encrypted_record_randomizers,
        state.executable(),
        local_data.leaf_randomizers().clone(),
    )
    .unwrap();

    // Check that the core check constraint system was satisfied.
    let mut inner_circuit_cs = TestConstraintSystem::<Fr>::new();

    let inner_circuit = InnerCircuit::new(inner_public_variables.clone(), inner_private_variables);
    inner_circuit
        .generate_constraints(&mut inner_circuit_cs.ns(|| "Inner circuit"))
        .unwrap();

    if !inner_circuit_cs.is_satisfied() {
        println!("=========================================================");
        println!(
            "Inner circuit num constraints: {:?}",
            inner_circuit_cs.num_constraints()
        );
        println!("Unsatisfied constraints:");
        println!("{}", inner_circuit_cs.which_is_unsatisfied().unwrap());
        println!("=========================================================");
    }

    println!("=========================================================");
    let num_constraints = inner_circuit_cs.num_constraints();
    println!("Inner circuit num constraints: {:?}", num_constraints);
    assert_eq!(191073, num_constraints);
    println!("=========================================================");

    assert!(inner_circuit_cs.is_satisfied());

    // Generate inner snark parameters and proof for verification in the outer snark
    let inner_snark_parameters = <Testnet2 as Network>::InnerSNARK::setup(
        &InnerCircuit::<Testnet2>::blank(),
        &mut SRS::CircuitSpecific(&mut rng),
    )
    .unwrap();

    let inner_snark_vk = inner_snark_parameters.1.clone();

    // NOTE: Do not change this to `Testnet2Parameters::inner_circuit_id()` as that will load the *saved* inner circuit VK.
    let inner_circuit_id = <Testnet2 as Network>::inner_circuit_id_crh()
        .hash_bits(&inner_snark_vk.to_minimal_bits())
        .unwrap();

    let inner_snark_proof =
        <Testnet2 as Network>::InnerSNARK::prove(&inner_snark_parameters.0, &inner_circuit, &mut rng).unwrap();

    // Verify that the inner circuit proof passes.
    assert!(
        <Testnet2 as Network>::InnerSNARK::verify(&inner_snark_vk, &inner_public_variables, &inner_snark_proof)
            .unwrap()
    );

    // Construct the outer circuit public and private variables.
    let outer_public_variables = OuterPublicVariables::new(&inner_public_variables, &inner_circuit_id);
    let outer_private_variables = OuterPrivateVariables::new(
        inner_snark_vk.clone(),
        inner_snark_proof,
        execution,
        state.executable().program_id(),
        local_data_root.clone(),
    );

    // Check that the proof check constraint system was satisfied.
    let mut outer_circuit_cs = TestConstraintSystem::<Fq>::new();

    execute_outer_circuit::<Testnet2, _>(
        &mut outer_circuit_cs.ns(|| "Outer circuit"),
        &outer_public_variables,
        &outer_private_variables,
    )
    .unwrap();

    if !outer_circuit_cs.is_satisfied() {
        println!("=========================================================");
        println!(
            "Outer circuit num constraints: {:?}",
            outer_circuit_cs.num_constraints()
        );
        println!("Unsatisfied constraints:");
        println!("{}", outer_circuit_cs.which_is_unsatisfied().unwrap());
        println!("=========================================================");
    }

    println!("=========================================================");
    let num_constraints = outer_circuit_cs.num_constraints();
    println!("Outer circuit num constraints: {:?}", num_constraints);
    assert_eq!(287976, num_constraints);
    println!("=========================================================");

    assert!(outer_circuit_cs.is_satisfied());
}
