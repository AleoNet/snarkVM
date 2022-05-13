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

use crate::{circuits::AleoDPC, InputPrivateVariables, InputPublicVariables, Network};
use snarkvm_circuits::{
    account::{Record, Signature},
    algorithms::{poseidon::ecies::ECIESPoseidonEncryption, MerklePath},
    prelude::*,
    Eject,
    Environment,
    Inject,
    Mode,
};
use snarkvm_utilities::{FromBytes, ToBytes};

// TODO (raychu86): TODOs for the input circuit:
//  - Add ciphertext, randomizer, view_key, etc to the Record circuit
//  - Add access to the LeafCRH and TwoToOneCRH circuits via `A: AleoDPC`
//    - We need this to use the merkle path circuits.
//  - Unify AleoDPC with Aleo
//  - Formalize `CustomDevnet`
//  - Split the following structs into different files

pub struct NewInputCircuit<A: AleoDPC, N: Network> {
    // Input public variables.
    pub public: InputCircuitPublicVariables<A>,

    // Input private variables.
    pub private: InputCircuitPrivateVariables<A, N>,
}

pub struct InputCircuitPublicVariables<A: AleoDPC> {
    // Input public variables.
    pub serial_number: Field<A>,
    pub input_value_commitment: Field<A>,
    pub ledger_root: Field<A>,
    pub local_transitions_root: Field<A>,
    pub program_id: Field<A>,
}

pub struct InputCircuitPrivateVariables<A: AleoDPC, N: Network> {
    // Input private variables.
    pub input_record: Record<A>,
    pub ledger_proof: LedgerProofCircuit<A, N>,
    pub signature: Signature<A>,
    pub input_value_commitment_randomness: Scalar<A>,
}

pub struct LedgerProofCircuit<E: Environment, N: Network> {
    ledger_root: Field<E>,
    ledger_root_inclusion_proof: MerklePath<E, N::LedgerRootTwoToOneCRHCircuit>,
    record_proof: RecordProofCircuit<E, N>,
}

pub struct RecordProofCircuit<E: Environment, N: Network> {
    block_hash: Field<E>,
    previous_block_hash: Field<E>,
    block_header_root: Field<E>,
    block_header_inclusion_proof: MerklePath<E, N::BlockHeaderRootTwoToOneCRHCircuit>,
    transactions_root: Field<E>,
    transactions_inclusion_proof: MerklePath<E, N::TransactionsRootTwoToOneCRHCircuit>,
    local_proof: LocalProofCircuit<E, N>,
}

pub struct LocalProofCircuit<E: Environment, N: Network> {
    transaction_id: Field<E>,
    transaction_inclusion_proof: MerklePath<E, N::TransactionIDTwoToOneCRHCircuit>,
    transition_id: Field<E>,
    transition_inclusion_proof: MerklePath<E, N::TransitionIDTwoToOneCRHCircuit>,
    commitment: Field<E>,
}

impl<A: AleoDPC, N: Network> Inject for NewInputCircuit<A, N> {
    type Primitive = (InputPublicVariables<N>, InputPrivateVariables<N>);

    /// Initializes an input circuit from the given mode and `(input_public_variables, input_private_variables)`.
    fn new(_mode: Mode, (input_public_variables, input_private_variables): Self::Primitive) -> Self {
        // TODO (raychu86): Handle base field and scalar field mismatches.

        // // Initialize the public variables.
        // let serial_number = Field::<A>::new(Mode::Public, **input_public_variables.serial_number());
        // let input_value_commitment =
        //     Field::<A>::new(Mode::Public, *input_public_variables.input_value_commitment().into());
        // let ledger_root = Field::<A>::new(Mode::Public, *input_public_variables.ledger_root());
        // let local_transitions_root = Field::<A>::new(Mode::Public, *input_public_variables.local_transitions_root());
        //
        // let program_id_bytes = input_public_variables
        //     .program_id
        //     .map_or(Ok(vec![0u8; N::PROGRAM_ID_SIZE_IN_BYTES]), |program_id| program_id.to_bytes_le())
        //     .unwrap();
        // let program_id = Field::<A>::new(Mode::Public, FromBytes::read_le(&program_id_bytes[..]).unwrap());
        //
        // let public = InputCircuitPublicVariables {
        //     serial_number,
        //     input_value_commitment,
        //     ledger_root,
        //     local_transitions_root,
        //     program_id,
        // };
        //
        // // Initialize the private variables.
        //
        // // TODO (raychu86): Fix placeholder usage of record attributes.
        // let input_record = Record::<A>::new(
        //     Address::parse(format!("{}.private", input_private_variables.input_record.owner()).as_str()).unwrap().1,
        //     I64::new(Mode::Private, input_private_variables.input_record.value().as_i64()),
        //     vec![Literal::<A>::from_str("10field.public")],
        // );
        // let signature = Signature::<A>::new(Mode::Private, input_private_variables.signature);
        // let input_value_commitment_randomness =
        //     Scalar::<A>::new(Mode::Private, input_private_variables.input_value_commitment_randomness);
        //
        // let native_ledger_proof = &input_private_variables.ledger_proof;
        //
        // let local_proof = LocalProofCircuit {
        //     transaction_id: Field::<A>::new(Mode::Private, *native_ledger_proof.transaction_id()),
        //     transaction_inclusion_proof: MerklePath::<A, N::TransactionIDTwoToOneCRHCircuit>::new(
        //         Mode::Private,
        //         (
        //             native_ledger_proof.transaction_inclusion_proof().position_list().collect::<Vec<_>>(),
        //             native_ledger_proof.transaction_inclusion_proof().path.clone(),
        //         ),
        //     ),
        //     transition_id: Field::<A>::new(Mode::Private, *native_ledger_proof.transition_id()),
        //     transition_inclusion_proof: MerklePath::<A, N::TransitionIDTwoToOneCRHCircuit>::new(
        //         Mode::Private,
        //         (
        //             native_ledger_proof.transition_inclusion_proof().position_list().collect::<Vec<_>>(),
        //             native_ledger_proof.transition_inclusion_proof().path.clone(),
        //         ),
        //     ),
        //     commitment: Field::<A>::new(Mode::Private, *native_ledger_proof.commitment()),
        // };
        //
        // let record_proof = RecordProofCircuit {
        //     block_hash: Field::<A>::new(Mode::Private, *native_ledger_proof.block_hash()),
        //     previous_block_hash: Field::<A>::new(Mode::Private, native_ledger_proof.previous_block_hash()),
        //     block_header_root: Field::<A>::new(Mode::Private, native_ledger_proof.block_header_root()),
        //     block_header_inclusion_proof: MerklePath::<A, N::BlockHeaderRootTwoToOneCRHCircuit>::new(
        //         Mode::Private,
        //         (
        //             native_ledger_proof.block_header_inclusion_proof().position_list().collect::<Vec<_>>(),
        //             native_ledger_proof.block_header_inclusion_proof().path.clone(),
        //         ),
        //     ),
        //     transactions_root: Field::<A>::new(Mode::Private, *native_ledger_proof.transactions_root()),
        //     transactions_inclusion_proof: MerklePath::<A, N::TransactionsRootTwoToOneCRHCircuit>::new(
        //         Mode::Private,
        //         (
        //             native_ledger_proof.transactions_inclusion_proof().position_list().collect::<Vec<_>>(),
        //             native_ledger_proof.transactions_inclusion_proof().path.clone(),
        //         ),
        //     ),
        //     local_proof,
        // };
        //
        // let ledger_proof = LedgerRootProofCircuit {
        //     ledger_root: Field::<A>::new(Mode::Private, *native_ledger_proof.ledger_root()),
        //     ledger_root_inclusion_proof: MerklePath::<A, N::LedgerRootTwoToOneCRHCircuit>::new(
        //         Mode::Private,
        //         (
        //             native_ledger_proof.ledger_root_inclusion_proof().position_list().collect::<Vec<_>>(),
        //             native_ledger_proof.ledger_root_inclusion_proof().path.clone(),
        //         ),
        //     ),
        //     record_proof,
        // };
        //
        // let private =
        //     InputCircuitPrivateVariables { input_record, signature, input_value_commitment_randomness, ledger_proof };
        //
        // Self { public, private }

        unimplemented!()
    }
}

impl<A: AleoDPC, N: Network> Eject for NewInputCircuit<A, N> {
    type Primitive = (InputPublicVariables<N>, InputPrivateVariables<N>);

    ///
    /// Ejects the mode of the input circuit.
    ///
    fn eject_mode(&self) -> Mode {
        unimplemented!()
    }

    ///
    /// Ejects the input circuit as `(input_public_variables, input_private_variables)`.
    ///
    fn eject_value(&self) -> Self::Primitive {
        unimplemented!()
    }
}

impl<A: AleoDPC, N: Network> NewInputCircuit<A, N> {
    pub fn execute(&self) {
        let public = &self.public;
        let private = &self.private;

        let valid = Boolean::<A>::new(Mode::Constant, true);

        let zero_value = I64::<A>::new(Mode::Constant, 0);
        let empty_payload_bits = vec![Boolean::<A>::new(Mode::Constant, false); N::RECORD_PAYLOAD_SIZE_IN_BYTES * 8];
        let empty_program_id = Field::<A>::new(Mode::Constant, Default::default());

        let record_owner = private.input_record.owner();
        let record_value = private.input_record.balance();
        let record_data = private.input_record.data();

        // TODO (raychu86): Implement is_dummy for the record.
        let given_is_dummy = Boolean::<A>::new(Mode::Constant, true);
        // TODO (raychu86): Split the record data into relevant parts. (ciphertext, program id, etc.)
        let record_payload_bits = vec![Boolean::<A>::new(Mode::Constant, false); N::RECORD_PAYLOAD_SIZE_IN_BYTES * 8];
        // TODO (raychu86): Derive the record view key from the record.
        let record_view_key = Field::<A>::new(Mode::Constant, Default::default());
        // TODO (raychu86): Derive the record randomizer from the record.
        let record_randomizer = Field::<A>::new(Mode::Constant, Default::default());
        // TODO (raychu86): Use the record program id
        let record_program_id = &public.program_id;

        let signature = &private.signature;

        // *******************************************************************
        // Check that the record is well-formed.
        // *******************************************************************
        let candidate_commitment = {
            // *******************************************************************
            // Convert the owner, dummy flag, value, payload, program ID, and randomizer into bits.
            // *******************************************************************
            // Perform noop safety checks.

            // If the input record is empty, enforce it has a value of 0
            let is_empty_value = record_value.is_equal(&zero_value);
            A::assert(Ternary::ternary(&given_is_dummy, &is_empty_value, &valid));

            // If the input record is empty, enforce it has an empty payload
            let is_empty_payload = record_payload_bits
                .iter()
                .zip(empty_payload_bits)
                .fold(Boolean::<A>::new(Mode::Constant, true), |result, (a, b)| result.bitand(&a.is_equal(&b)));
            A::assert(Ternary::ternary(&given_is_dummy, &is_empty_payload, &valid));

            // If the input record is empty, enforce it has an empty program ID
            let is_empty_program_id = record_program_id.is_equal(&empty_program_id);
            A::assert(Ternary::ternary(&given_is_dummy, &is_empty_program_id, &valid));

            // Ensure the program ID matches the declared program ID (conditionally).
            let is_equivalent_program_id = record_program_id.is_equal(&public.program_id);
            A::assert(Ternary::ternary(&given_is_dummy.clone().not(), &is_equivalent_program_id, &valid));

            // *******************************************************************
            // Compute the record commitment and check that it matches the declared commitment.
            // *******************************************************************

            // TODO (raychu86): Move this out to the Aleo trait.
            let encryption_scheme = ECIESPoseidonEncryption::<A, 4>::setup();

            // Derive the record ciphertext.
            let encoded_value = encryption_scheme.encode_message(&record_value.to_bits_le());
            let encoded_payload = encryption_scheme.encode_message(&record_payload_bits);

            let mut plaintext = Vec::with_capacity(1 + encoded_value.len() + encoded_payload.len());
            plaintext.push(record_owner.0.to_x_coordinate());
            plaintext.extend_from_slice(&encoded_value);
            plaintext.extend_from_slice(&encoded_payload);

            let ciphertext = encryption_scheme.encrypt(record_view_key, &plaintext);

            // Derive the record view key commitment.
            // TODO (raychu86): Implement the record view key commitment.
            // let record_view_key_commitment = encryption_scheme.commitment(&record_view_key);

            // Compute the record commitment
            let mut commitment_input = vec![];

            commitment_input.extend_from_slice(&record_randomizer.to_bits_le());
            // commitment_input.extend_from_slice(&record_view_key_commitment_bytes);
            commitment_input.extend_from_slice(&ciphertext.to_bits_le());
            commitment_input.extend_from_slice(&public.program_id.to_bits_le());
            commitment_input.extend_from_slice(&[given_is_dummy]);

            A::hash_record_commitment_bhp(&commitment_input)
        };

        // ********************************************************************
        // Check that the serial number is derived correctly.
        // ********************************************************************
        {
            // Compute sk_prf := RO(G^sk_sig || G^r_sig).
            let sk_prf = A::hash_psd4(&[signature.pk_sig().to_x_coordinate(), signature.pr_sig().to_x_coordinate()]);

            let candidate_serial_number = A::prf_serial_number_psd(&sk_prf, &vec![candidate_commitment.clone()]);

            A::assert_eq(&candidate_serial_number, &public.serial_number);
        }

        // **********************************************************************************
        // Check that the commitment appears on the ledger or prior transition,
        // i.e., the membership witness is valid with respect to the ledger root.
        // **********************************************************************************
        {
            let ledger_proof = &private.ledger_proof;
            let record_proof = &ledger_proof.record_proof;
            let local_proof = &record_proof.local_proof;

            // TODO (raychu86): Implement these checks.
            // let candidate_transition_id = local_proof.transition_inclusion_proof.to_root(
            //     &TRANSITION_ID_CRH,
            //     &TRANSITION_ID_TWO_TO_ONE_CRH,
            //     &candidate_commitment.to_bits_le(),
            // );
        }

        // ********************************************************************
        // Check that the input value commitment is derived correctly.
        // ********************************************************************
        {
            let value_commitment_randomness = &private.input_value_commitment_randomness;
            let value_bits = &private.input_record.balance().to_bits_le();
            let given_value_commitment = &public.input_value_commitment;

            let candidate_value_commitment = A::commit_value_ped(value_bits, value_commitment_randomness);

            A::assert_eq(given_value_commitment, candidate_value_commitment);
        }

        // *******************************************************************
        // Check that the signature is valid.
        // *******************************************************************
        {
            let mut signature_message = Vec::new();
            signature_message.push(Literal::<A>::Field(candidate_commitment));
            signature_message.push(Literal::<A>::Field(public.program_id.clone()));

            A::assert(signature.verify(record_owner, &signature_message))
        }
    }
}

#[cfg(test)]
mod tests {}
