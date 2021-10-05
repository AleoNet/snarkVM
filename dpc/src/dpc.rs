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
use snarkvm_utilities::ToBytes;

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::marker::PhantomData;

pub struct DPC<N: Network>(PhantomData<N>);

impl<N: Network> DPCScheme<N> for DPC<N> {
    type Account = Account<N>;
    type LedgerProof = LedgerProof<N>;
    type StateTransition = StateTransition<N>;

    /// Returns an authorization to execute a state transition.
    fn authorize<R: Rng + CryptoRng>(
        private_keys: &Vec<<Self::Account as AccountScheme>::PrivateKey>,
        transition: &Self::StateTransition,
        rng: &mut R,
    ) -> Result<Vec<N::AccountSignature>> {
        // Keep a cursor for the private keys.
        let mut index = 0;

        // Construct the signature message.
        let signature_message = transition.kernel().to_transaction_id()?.to_bytes_le()?;

        // Sign the transaction kernel to authorize the transaction.
        let mut signatures = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for noop_private_key in transition.noop_private_keys().iter().take(N::NUM_INPUT_RECORDS) {
            // Fetch the correct private key.
            let private_key = match noop_private_key {
                Some(noop_private_key) => noop_private_key,
                None => {
                    let private_key = &private_keys[index];
                    index += 1;
                    private_key
                }
            };

            // Sign the signature message.
            signatures.push(private_key.sign(&signature_message, rng)?);
        }

        // Return the transaction authorization.
        Ok(signatures)
    }

    /// Returns a transaction by executing an authorized state transition.
    fn execute<R: Rng + CryptoRng>(
        signatures: Vec<N::AccountSignature>,
        transition: &Self::StateTransition,
        ledger_proof: Self::LedgerProof,
        rng: &mut R,
    ) -> Result<Transaction<N>> {
        debug_assert_eq!(N::NUM_INPUT_RECORDS, signatures.len());

        let execution_timer = start_timer!(|| "DPC::execute");

        // Construct the ledger witnesses.
        let block_hash = ledger_proof.block_hash();

        // Generate the transaction ID.
        let transaction_id = transition.kernel().to_transaction_id()?;

        // Execute the program circuit.
        let execution = transition.executable().execute(PublicVariables::new(transaction_id))?;

        // Construct the inner circuit public and private variables.
        let inner_public_variables =
            InnerPublicVariables::new(transaction_id, block_hash, Some(transition.executable().program_id()))?;
        let inner_private_variables = InnerPrivateVariables::new(
            transition.kernel(),
            transition.input_records().clone(),
            ledger_proof,
            signatures,
            transition.output_records().clone(),
            transition.ciphertext_randomizers.clone(),
            &transition.executable(),
        )?;

        // Compute the inner circuit proof.
        let inner_proof = N::InnerSNARK::prove(
            N::inner_circuit_proving_key(),
            &InnerCircuit::<N>::new(inner_public_variables.clone(), inner_private_variables),
            rng,
        )?;

        // Verify that the inner circuit proof passes.
        assert!(N::InnerSNARK::verify(
            N::inner_circuit_verifying_key(),
            &inner_public_variables,
            &inner_proof
        )?);

        // Construct the outer circuit public and private variables.
        let outer_public_variables = OuterPublicVariables::new(&inner_public_variables, *N::inner_circuit_id());
        let outer_private_variables =
            OuterPrivateVariables::new(N::inner_circuit_verifying_key().clone(), inner_proof, execution);

        let transaction_proof = N::OuterSNARK::prove(
            N::outer_circuit_proving_key(),
            &OuterCircuit::<N>::new(outer_public_variables, outer_private_variables),
            rng,
        )?;

        let metadata = TransactionMetadata::new(block_hash, *N::inner_circuit_id());
        end_timer!(execution_timer);

        Transaction::from(
            transition.kernel().clone(),
            metadata,
            transition.ciphertexts.clone(),
            transaction_proof,
        )
    }
}
