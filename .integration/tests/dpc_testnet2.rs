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
use snarkvm_dpc::{prelude::*, testnet2::*};
use snarkvm_fields::ToConstraintField;
use snarkvm_integration::testnet2::*;
use snarkvm_ledger::{ledger::*, prelude::*};
use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::Result;
use rand::SeedableRng;
use rand_chacha::ChaChaRng;
use std::time::{SystemTime, UNIX_EPOCH};

fn testnet2_inner_circuit_id() -> Result<Vec<u8>> {
    let inner_circuit_id = <Testnet2Parameters as Parameters>::inner_circuit_id_crh()
        .hash_field_elements(&<Testnet2Parameters as Parameters>::inner_circuit_verifying_key().to_field_elements()?)?;
    Ok(inner_circuit_id.to_bytes_le()?)
}

/// TODO (howardwu): Update this to the correct inner circuit ID when the final parameters are set.
#[ignore]
#[test]
fn test_testnet2_inner_circuit_sanity_check() {
    let expected_testnet2_inner_circuit_id = vec![
        70, 187, 221, 37, 4, 78, 200, 68, 34, 184, 229, 110, 24, 7, 142, 8, 62, 42, 234, 231, 96, 86, 201, 94, 143,
        197, 248, 117, 32, 218, 44, 219, 109, 191, 72, 112, 157, 76, 212, 91, 7, 14, 32, 183, 79, 1, 194, 0,
    ];
    let candidate_testnet2_inner_circuit_id = testnet2_inner_circuit_id().unwrap();
    assert_eq!(expected_testnet2_inner_circuit_id, candidate_testnet2_inner_circuit_id);
}

#[test]
fn dpc_testnet2_integration_test() {
    let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

    // Generate accounts.
    let genesis_account = Account::new(&mut rng).unwrap();
    let recipient = Account::new(&mut rng).unwrap();

    // Create a genesis block.
    let genesis_block = Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            merkle_root_hash: MerkleRootHash([0u8; 32]),
            pedersen_merkle_root_hash: PedersenMerkleRootHash([0u8; 32]),
            proof: ProofOfSuccinctWork([0u8; 972]),
            time: 0,
            difficulty_target: 0xFFFF_FFFF_FFFF_FFFF_u64,
            nonce: 0,
        },
        transactions: Transactions::new(),
    };

    let ledger = Ledger::<Testnet2Parameters, MemDb>::new(None, genesis_block).unwrap();

    // Generate or load DPC.
    let dpc = setup_or_load_dpc(false, &mut rng);

    // Generate dummy input records having as address the genesis address.
    let old_private_keys = vec![genesis_account.private_key.clone(); Testnet2Parameters::NUM_INPUT_RECORDS];

    let mut joint_serial_numbers = vec![];
    let mut input_records = vec![];
    for i in 0..Testnet2Parameters::NUM_INPUT_RECORDS {
        let input_record = Record::new(
            &dpc.noop_program,
            genesis_account.address.clone(),
            true, // The input record is dummy
            0,
            Payload::default(),
            <Testnet2Parameters as Parameters>::serial_number_nonce_crh()
                .hash(&[64u8 + (i as u8); 1])
                .unwrap(),
            &mut rng,
        )
        .unwrap();

        let (sn, _) = input_record.to_serial_number(&old_private_keys[i]).unwrap();
        joint_serial_numbers.extend_from_slice(&to_bytes_le![sn].unwrap());

        input_records.push(input_record);
    }

    // Construct new records.

    // Set the new records' program to be the "always-accept" program.
    let mut output_records = vec![];
    for j in 0..Testnet2Parameters::NUM_OUTPUT_RECORDS {
        output_records.push(
            Record::new_full(
                &dpc.noop_program,
                recipient.address.clone(),
                false,
                10,
                Payload::default(),
                (Testnet2Parameters::NUM_INPUT_RECORDS + j) as u8,
                joint_serial_numbers.clone(),
                &mut rng,
            )
            .unwrap(),
        );
    }

    // Offline execution to generate a transaction authorization.
    let authorization = dpc
        .authorize(&old_private_keys, input_records, output_records, None, &mut rng)
        .unwrap();

    // Generate the local data.
    let local_data = authorization.to_local_data(&mut rng).unwrap();

    // Generate the program proofs
    let mut program_proofs = vec![];
    for i in 0..Testnet2Parameters::NUM_TOTAL_RECORDS {
        let public_variables = ProgramPublicVariables::new(local_data.root(), i as u8);
        program_proofs.push(
            dpc.noop_program
                .execute(0, &public_variables, &NoopPrivateVariables::new())
                .unwrap(),
        );
    }

    let new_records = authorization.output_records.clone();

    let transaction = dpc
        .execute(
            &old_private_keys,
            authorization,
            &local_data,
            program_proofs,
            &ledger,
            &mut rng,
        )
        .unwrap();

    // Check that the transaction is serialized and deserialized correctly
    let transaction_bytes = to_bytes_le![transaction].unwrap();
    let recovered_transaction = Testnet2Transaction::read_le(&transaction_bytes[..]).unwrap();
    assert_eq!(transaction, recovered_transaction);

    // Check that new_records can be decrypted from the transaction
    {
        let encrypted_records = transaction.encrypted_records();
        let new_account_private_keys = vec![recipient.private_key; Testnet2Parameters::NUM_OUTPUT_RECORDS];

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

    let mut merkle_root_bytes = [0u8; 32];
    merkle_root_bytes[..].copy_from_slice(&merkle_root(&transaction_ids));

    let time = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards")
        .as_secs() as i64;

    let header = BlockHeader {
        previous_block_hash: previous_block.header.get_hash(),
        merkle_root_hash: MerkleRootHash(merkle_root_bytes),
        time,
        difficulty_target: previous_block.header.difficulty_target,
        nonce: 0,
        pedersen_merkle_root_hash: PedersenMerkleRootHash([0u8; 32]),
        proof: ProofOfSuccinctWork([0u8; 972]),
    };

    assert!(dpc.verify_transactions(&transactions.0, &ledger));

    let block = Block { header, transactions };

    ledger.insert_and_commit(&block).unwrap();
    assert_eq!(ledger.block_height(), 1);
}

#[test]
fn test_testnet_2_transaction_authorization_serialization() {
    let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

    let dpc = Testnet2DPC::load(false).unwrap();

    // Generate metadata and an account for a dummy initial record.
    let test_account = Account::new(&mut rng).unwrap();

    let old_private_keys = vec![test_account.private_key.clone(); Testnet2Parameters::NUM_INPUT_RECORDS];

    // Set the input records for our transaction to be the initial dummy records.
    let mut joint_serial_numbers = vec![];
    let mut input_records = vec![];
    for i in 0..Testnet2Parameters::NUM_INPUT_RECORDS {
        let old_record = Record::new(
            &dpc.noop_program,
            test_account.address.clone(),
            true,
            0,
            Payload::default(),
            <Testnet2Parameters as Parameters>::serial_number_nonce_crh()
                .hash(&[0u8; 1])
                .unwrap(),
            &mut rng,
        )
        .unwrap();

        let (sn, _) = old_record.to_serial_number(&old_private_keys[i]).unwrap();
        joint_serial_numbers.extend_from_slice(&to_bytes_le![sn].unwrap());

        input_records.push(old_record);
    }

    // Construct new records.

    // Set the new record's program to be the "always-accept" program.
    let mut output_records = vec![];
    for j in 0..Testnet2Parameters::NUM_OUTPUT_RECORDS {
        output_records.push(
            Record::new_full(
                &dpc.noop_program,
                test_account.address.clone(),
                false,
                10,
                Payload::default(),
                (Testnet2Parameters::NUM_INPUT_RECORDS + j) as u8,
                joint_serial_numbers.clone(),
                &mut rng,
            )
            .unwrap(),
        );
    }

    // Generate transaction authorization
    let transaction_authorization = dpc
        .authorize(&old_private_keys, input_records, output_records, None, &mut rng)
        .unwrap();

    // Serialize the transaction kernel
    let recovered_transaction_authorization =
        FromBytes::read_le(&transaction_authorization.to_bytes_le().unwrap()[..]).unwrap();

    assert_eq!(transaction_authorization, recovered_transaction_authorization);
}

#[test]
fn test_testnet2_dpc_execute_constraints() {
    let mut rng = ChaChaRng::seed_from_u64(1231275789u64);

    let dpc = Testnet2DPC::setup(&mut rng).unwrap();

    let alternate_noop_program = NoopProgram::<Testnet2Parameters>::setup(&mut rng).unwrap();

    // Generate metadata and an account for a dummy initial record.
    let dummy_account = Account::new(&mut rng).unwrap();

    let genesis_block = Block {
        header: BlockHeader {
            previous_block_hash: BlockHeaderHash([0u8; 32]),
            merkle_root_hash: MerkleRootHash([0u8; 32]),
            time: 0,
            difficulty_target: 0xFFFF_FFFF_FFFF_FFFF_u64,
            nonce: 0,
            pedersen_merkle_root_hash: PedersenMerkleRootHash([0u8; 32]),
            proof: ProofOfSuccinctWork([0u8; 972]),
        },
        transactions: Transactions::new(),
    };

    // Use genesis block to initialize the ledger.
    let ledger = Ledger::<Testnet2Parameters, MemDb>::new(None, genesis_block).unwrap();

    let private_keys = vec![dummy_account.private_key; Testnet2Parameters::NUM_INPUT_RECORDS];

    // Set the input records for our transaction to be the initial dummy records.
    let mut joint_serial_numbers = vec![];
    let mut input_records = vec![];
    for i in 0..Testnet2Parameters::NUM_INPUT_RECORDS {
        let input_record = Record::new(
            &alternate_noop_program,
            dummy_account.address.clone(),
            true,
            0,
            Payload::default(),
            <Testnet2Parameters as Parameters>::serial_number_nonce_crh()
                .hash(&[0u8; 1])
                .unwrap(),
            &mut rng,
        )
        .unwrap();

        let (sn, _) = input_record.to_serial_number(&private_keys[i]).unwrap();
        joint_serial_numbers.extend_from_slice(&to_bytes_le![sn].unwrap());

        input_records.push(input_record);
    }

    // Create an account for an actual new record.
    let new_account = Account::new(&mut rng).unwrap();

    // Construct new records.

    // Set the new record's program to be the "always-accept" program.
    let mut output_records = vec![];
    for j in 0..Testnet2Parameters::NUM_OUTPUT_RECORDS {
        output_records.push(
            Record::new_full(
                &dpc.noop_program,
                new_account.address.clone(),
                false,
                10,
                Payload::default(),
                (Testnet2Parameters::NUM_INPUT_RECORDS + j) as u8,
                joint_serial_numbers.clone(),
                &mut rng,
            )
            .unwrap(),
        );
    }

    let authorization = dpc
        .authorize(&private_keys, input_records, output_records, None, &mut rng)
        .unwrap();

    // Generate the local data.
    let local_data = authorization.to_local_data(&mut rng).unwrap();

    // Generate the program proofs
    let mut program_proofs = vec![];
    for i in 0..Testnet2Parameters::NUM_INPUT_RECORDS {
        let public_variables = ProgramPublicVariables::new(local_data.root(), i as u8);
        program_proofs.push(
            alternate_noop_program
                .execute(0, &public_variables, &NoopPrivateVariables::new())
                .unwrap(),
        );
    }
    for j in 0..Testnet2Parameters::NUM_OUTPUT_RECORDS {
        let public_variables =
            ProgramPublicVariables::new(local_data.root(), (Testnet2Parameters::NUM_INPUT_RECORDS + j) as u8);
        program_proofs.push(
            dpc.noop_program
                .execute(0, &public_variables, &NoopPrivateVariables::new())
                .unwrap(),
        );
    }

    // Compute the program commitment.
    let (program_commitment, program_randomness) = authorization.to_program_commitment(&mut rng).unwrap();

    // Compute the encrypted records.
    let (_encrypted_records, encrypted_record_hashes, encrypted_record_randomizers) =
        authorization.to_encrypted_records(&mut rng).unwrap();

    let TransactionAuthorization {
        kernel,
        input_records: old_records,
        output_records: new_records,
        signatures: _,
    } = authorization;

    let TransactionKernel {
        network_id,
        serial_numbers,
        commitments,
        value_balance,
        memo,
    } = kernel;

    let local_data_root = local_data.root();

    // Construct the ledger witnesses
    let ledger_digest = ledger.latest_digest().expect("could not get digest");

    // Generate the ledger membership witnesses
    let mut old_witnesses = Vec::with_capacity(Testnet2Parameters::NUM_INPUT_RECORDS);

    // Compute the ledger membership witness and serial number from the old records.
    for record in old_records.iter() {
        if record.is_dummy() {
            old_witnesses.push(MerklePath::default());
        } else {
            let witness = ledger.prove_cm(&record.commitment()).unwrap();
            old_witnesses.push(witness);
        }
    }

    //////////////////////////////////////////////////////////////////////////
    // Check that the core check constraint system was satisfied.
    let mut inner_circuit_cs = TestConstraintSystem::<Fr>::new();

    execute_inner_circuit(
        &mut inner_circuit_cs.ns(|| "Inner circuit"),
        &ledger_digest,
        &old_records,
        &old_witnesses,
        &private_keys,
        &serial_numbers,
        &new_records,
        &commitments,
        &encrypted_record_randomizers,
        &encrypted_record_hashes,
        &program_commitment,
        &program_randomness,
        &local_data_root,
        &local_data.leaf_randomizers(),
        &memo,
        value_balance,
        network_id,
    )
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

    {
        println!("=========================================================");
        let num_constraints = inner_circuit_cs.num_constraints();
        println!("Inner circuit num constraints: {:?}", num_constraints);
        assert_eq!(283217, num_constraints);
        println!("=========================================================");
    }

    assert!(inner_circuit_cs.is_satisfied());

    // Generate inner snark parameters and proof for verification in the outer snark
    let inner_snark_parameters = <Testnet2Parameters as Parameters>::InnerSNARK::setup(
        &InnerCircuit::<Testnet2Parameters>::blank(),
        &mut SRS::CircuitSpecific(&mut rng),
    )
    .unwrap();

    let inner_snark_vk: <<Testnet2Parameters as Parameters>::InnerSNARK as SNARK>::VerifyingKey =
        inner_snark_parameters.1.clone().into();

    let inner_snark_vk_field_elements = inner_snark_vk.to_field_elements().unwrap();

    let inner_circuit_id = <Testnet2Parameters as Parameters>::inner_circuit_id_crh()
        .hash_field_elements(&inner_snark_vk_field_elements)
        .unwrap();

    let inner_snark_proof = <Testnet2Parameters as Parameters>::InnerSNARK::prove(
        &inner_snark_parameters.0,
        &InnerCircuit::new(
            ledger_digest,
            old_records,
            old_witnesses,
            private_keys,
            serial_numbers.clone(),
            new_records,
            commitments.clone(),
            encrypted_record_randomizers,
            encrypted_record_hashes.clone(),
            program_commitment,
            program_randomness,
            local_data_root.clone(),
            local_data.leaf_randomizers().clone(),
            memo,
            value_balance,
            network_id,
        ),
        &mut rng,
    )
    .unwrap();

    // Check that the proof check constraint system was satisfied.
    let mut outer_circuit_cs = TestConstraintSystem::<Fq>::new();

    execute_outer_circuit::<Testnet2Parameters, _>(
        &mut outer_circuit_cs.ns(|| "Outer circuit"),
        &ledger_digest,
        &serial_numbers,
        &commitments,
        &encrypted_record_hashes,
        &memo,
        value_balance,
        network_id,
        &inner_snark_vk,
        &inner_snark_proof,
        &program_proofs,
        &program_commitment,
        &program_randomness,
        &local_data_root,
        &inner_circuit_id,
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

    {
        println!("=========================================================");
        let num_constraints = outer_circuit_cs.num_constraints();
        println!("Outer circuit num constraints: {:?}", num_constraints);
        assert_eq!(878967, num_constraints);
        println!("=========================================================");
    }

    assert!(outer_circuit_cs.is_satisfied());
}
