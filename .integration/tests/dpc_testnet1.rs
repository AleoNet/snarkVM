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

use snarkvm_algorithms::{merkle_tree::MerklePath, prelude::*};
use snarkvm_curves::bls12_377::{Fq, Fr};
use snarkvm_dpc::{prelude::*, testnet1::*};
use snarkvm_ledger::{ledger::*, prelude::*};
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes, ToMinimalBits};

use rand::SeedableRng;
use rand_chacha::ChaChaRng;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn test_testnet1_inner_circuit_id_sanity_check() {
    let expected_inner_circuit_id = vec![
        248, 38, 233, 209, 152, 143, 211, 182, 12, 9, 67, 81, 141, 63, 83, 73, 202, 36, 42, 241, 145, 34, 232, 155, 99,
        85, 212, 0, 242, 37, 246, 65, 110, 96, 43, 131, 129, 55, 252, 114, 227, 62, 168, 22, 183, 193, 178, 0,
    ];
    let candidate_inner_circuit_id = <Testnet1Parameters as Parameters>::inner_circuit_id()
        .to_bytes_le()
        .unwrap();
    assert_eq!(expected_inner_circuit_id, candidate_inner_circuit_id);
}

#[test]
fn dpc_testnet1_integration_test() {
    let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

    // Create a genesis block.
    let genesis_block = Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            transactions_root: PedersenMerkleRootHash([0u8; 32]),
            commitments_root: MerkleRoot([0u8; 32]),
            serial_numbers_root: MerkleRoot([0u8; 32]),
            metadata: BlockHeaderMetadata::new(0, 0xFFFF_FFFF_FFFF_FFFF_u64, 0),
            proof: ProofOfSuccinctWork::default(),
        },
        transactions: Transactions::new(),
    };

    let ledger = Ledger::<Testnet1Parameters, MemDb>::new(None, genesis_block).unwrap();

    let recipient = Account::new(&mut rng).unwrap();
    let amount = AleoAmount::from_bytes(10 as i64);
    let state = StateTransition::builder()
        .add_output(Output::new(recipient.address, amount, Payload::default(), None).unwrap())
        .add_output(Output::new(recipient.address, amount, Payload::default(), None).unwrap())
        .build(&mut rng)
        .unwrap();
    let authorization = DPC::authorize(&vec![], &state, &mut rng).unwrap();

    let new_records = authorization.output_records.clone();

    let transaction = DPC::execute(authorization, state.executables(), &ledger, &mut rng).unwrap();

    // Check that the transaction is serialized and deserialized correctly
    let transaction_bytes = to_bytes_le![transaction].unwrap();
    let recovered_transaction = Testnet1Transaction::read_le(&transaction_bytes[..]).unwrap();
    assert_eq!(transaction, recovered_transaction);

    // Check that new_records can be decrypted from the transaction.
    {
        let encrypted_records = transaction.encrypted_records();
        let new_account_private_keys = vec![recipient.private_key(); Testnet1Parameters::NUM_OUTPUT_RECORDS];

        for ((encrypted_record, private_key), new_record) in
            encrypted_records.iter().zip(new_account_private_keys).zip(new_records)
        {
            let account_view_key = ViewKey::from_private_key(&private_key).unwrap();
            let decrypted_record = encrypted_record.decrypt(&account_view_key).unwrap();
            assert_eq!(decrypted_record, new_record);
        }
    }

    // Craft the block

    let previous_block = ledger.latest_block().unwrap();

    let mut transactions = Transactions::new();
    transactions.push(transaction);

    let transaction_ids = transactions.to_transaction_ids().unwrap();

    let time = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards")
        .as_secs() as i64;

    // Construct new_commitments_tree
    let transaction_commitments = transactions
        .0
        .iter()
        .map(|t| t.commitments().to_owned())
        .flatten()
        .collect();
    let new_commitments_tree = ledger.build_new_commitment_tree(transaction_commitments).unwrap();

    // Construct new_serial_numbers_tree
    let transaction_serial_numbers = transactions
        .0
        .iter()
        .map(|t| t.serial_numbers().to_owned())
        .flatten()
        .collect();
    let new_serial_numbers_tree = ledger.build_new_serial_number_tree(transaction_serial_numbers).unwrap();

    let header = BlockHeader {
        previous_block_hash: previous_block.header.to_hash().unwrap(),
        transactions_root: pedersen_merkle_root(&transaction_ids),
        commitments_root: MerkleRoot::from_element(new_commitments_tree.root()),
        serial_numbers_root: MerkleRoot::from_element(new_serial_numbers_tree.root()),
        metadata: BlockHeaderMetadata::new(time, previous_block.header.metadata.difficulty_target, 0),
        proof: ProofOfSuccinctWork::default(),
    };

    assert!(DPC::verify_transactions(&transactions.0, &ledger));

    let block = Block { header, transactions };

    ledger.insert_and_commit(&block).unwrap();
    assert_eq!(ledger.block_height(), 1);
}

#[test]
fn test_testnet1_dpc_execute_constraints() {
    let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

    let genesis_block = Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            transactions_root: PedersenMerkleRootHash([0u8; 32]),
            commitments_root: MerkleRoot([0u8; 32]),
            serial_numbers_root: MerkleRoot([0u8; 32]),
            metadata: BlockHeaderMetadata::new(0, 0xFFFF_FFFF_FFFF_FFFF_u64, 0),
            proof: ProofOfSuccinctWork::default(),
        },
        transactions: Transactions::new(),
    };

    // Use genesis block to initialize the ledger.
    let ledger = Ledger::<Testnet1Parameters, MemDb>::new(None, genesis_block).unwrap();

    let recipient = Account::new(&mut rng).unwrap();
    let amount = AleoAmount::from_bytes(10 as i64);

    let state = StateTransition::builder()
        .add_output(Output::new(recipient.address, amount, Payload::default(), None).unwrap())
        .add_output(Output::new(recipient.address, amount, Payload::default(), None).unwrap())
        .build(&mut rng)
        .unwrap();

    let authorization = DPC::<Testnet1Parameters>::authorize(&vec![], &state, &mut rng).unwrap();

    // Generate the local data.
    let local_data = authorization.to_local_data(&mut rng).unwrap();

    // Execute the programs.
    let mut executions = Vec::with_capacity(Testnet1Parameters::NUM_TOTAL_RECORDS);
    for (i, executable) in state.executables().iter().enumerate() {
        executions.push(executable.execute(i as u8, &local_data).unwrap());
    }

    // Compute the program commitment.
    let (program_commitment, program_randomness) = authorization.to_program_commitment(&mut rng).unwrap();

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

    // Construct the ledger witnesses
    let ledger_digest = ledger.latest_digest().expect("could not get digest");

    // Generate the ledger membership witnesses
    let mut old_witnesses = Vec::with_capacity(Testnet1Parameters::NUM_INPUT_RECORDS);

    // Compute the ledger membership witness and serial number from the input records.
    for record in input_records.iter() {
        if record.is_dummy() {
            old_witnesses.push(MerklePath::default());
        } else {
            let witness = ledger.prove_cm(&record.commitment()).unwrap();
            old_witnesses.push(witness);
        }
    }

    //////////////////////////////////////////////////////////////////////////

    // Construct the inner circuit public and private variables.
    let inner_public_variables = InnerPublicVariables::new(
        &kernel,
        &ledger_digest,
        &encrypted_record_hashes,
        Some(program_commitment),
        Some(local_data.root().clone()),
    )
    .unwrap();
    let inner_private_variables = InnerPrivateVariables::new(
        input_records.clone(),
        old_witnesses,
        signatures,
        output_records.clone(),
        encrypted_record_randomizers,
        program_randomness.clone(),
        local_data.leaf_randomizers().clone(),
    );

    // Check that the core check constraint system was satisfied.
    let mut inner_circuit_cs = TestConstraintSystem::<Fr>::new();

    execute_inner_circuit(
        &mut inner_circuit_cs.ns(|| "Inner circuit"),
        &inner_public_variables,
        &inner_private_variables,
    )
    .unwrap();

    if !inner_circuit_cs.is_satisfied() {
        println!("=========================================================");
        println!("Unsatisfied constraints:");
        println!("{}", inner_circuit_cs.which_is_unsatisfied().unwrap());
        println!("=========================================================");
    }

    println!("=========================================================");
    let num_constraints = inner_circuit_cs.num_constraints();
    println!("Inner circuit num constraints: {:?}", num_constraints);
    assert_eq!(283473, num_constraints);
    println!("=========================================================");

    assert!(inner_circuit_cs.is_satisfied());

    // Generate inner snark parameters and proof for verification in the outer snark
    let inner_snark_parameters = <Testnet1Parameters as Parameters>::InnerSNARK::setup(
        &InnerCircuit::<Testnet1Parameters>::blank(),
        &mut SRS::CircuitSpecific(&mut rng),
    )
    .unwrap();

    let inner_snark_vk = inner_snark_parameters.1.clone();

    // NOTE: Do not change this to `Testnet1Parameters::inner_circuit_id()` as that will load the *saved* inner circuit VK.
    let inner_circuit_id = <Testnet1Parameters as Parameters>::inner_circuit_id_crh()
        .hash_bits(&inner_snark_vk.to_minimal_bits())
        .unwrap();

    let inner_snark_proof = <Testnet1Parameters as Parameters>::InnerSNARK::prove(
        &inner_snark_parameters.0,
        &InnerCircuit::new(inner_public_variables.clone(), inner_private_variables),
        &mut rng,
    )
    .unwrap();

    // Construct the outer circuit public and private variables.
    let outer_public_variables = OuterPublicVariables::new(&inner_public_variables, &inner_circuit_id);
    let outer_private_variables = OuterPrivateVariables::new(
        inner_snark_vk.clone(),
        inner_snark_proof,
        executions.to_vec(),
        program_commitment.clone(),
        program_randomness,
        local_data_root.clone(),
    );

    // Check that the proof check constraint system was satisfied.
    let mut outer_circuit_cs = TestConstraintSystem::<Fq>::new();

    execute_outer_circuit::<Testnet1Parameters, _>(
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
    assert_eq!(515990, num_constraints);
    println!("=========================================================");

    assert!(outer_circuit_cs.is_satisfied());
}
