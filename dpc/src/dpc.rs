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

impl<N: Network> DPC<N> {
    /// Returns an authorization to execute a state transition.
    pub fn authorize<R: Rng + CryptoRng>(
        private_keys: &Vec<PrivateKey<N>>,
        transition: &StateTransition<N>,
        rng: &mut R,
    ) -> Result<Vec<N::AccountSignature>> {
        // Keep a cursor for the private keys.
        let mut index = 0;

        // Construct the signature message.
        let signature_message = transition.kernel().to_transaction_id()?.to_bytes_le()?;

        // Sign the transaction kernel to authorize the transaction.
        let mut signatures = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for noop_signature in transition.noop_signatures().iter().take(N::NUM_INPUT_RECORDS) {
            // Sign the signature message.
            signatures.push(match noop_signature {
                Some(noop_signature) => noop_signature.clone(),
                None => {
                    // Fetch the correct private key.
                    let private_key = &private_keys[index];
                    index += 1;

                    private_key.sign(&signature_message, rng)?
                }
            });
        }

        Ok(signatures)
    }

    /// Returns a transaction by executing an authorized state transition.
    pub fn execute<R: Rng + CryptoRng>(
        signatures: Vec<N::AccountSignature>,
        transition: &StateTransition<N>,
        ledger_proof: LedgerProof<N>,
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
        let inner_public = InnerPublicVariables::new(transaction_id, block_hash, Some(execution.program_id))?;
        let inner_private = InnerPrivateVariables::new(transition, ledger_proof, signatures)?;
        let inner_circuit = InnerCircuit::<N>::new(inner_public.clone(), inner_private);

        // Compute the inner circuit proof, and verify that the inner proof passes.
        let inner_proof = N::InnerSNARK::prove(N::inner_proving_key(), &inner_circuit, rng)?;
        assert!(N::InnerSNARK::verify(
            N::inner_verifying_key(),
            &inner_public,
            &inner_proof
        )?);

        // Construct the outer circuit public and private variables.
        let outer_public = OuterPublicVariables::new(&inner_public, *N::inner_circuit_id());
        let outer_private = OuterPrivateVariables::new(N::inner_verifying_key().clone(), inner_proof, execution);
        let outer_circuit = OuterCircuit::<N>::new(outer_public, outer_private);

        let transaction_proof = N::OuterSNARK::prove(N::outer_proving_key(), &outer_circuit, rng)?;
        end_timer!(execution_timer);

        Transaction::from(
            transition.kernel().clone(),
            block_hash,
            *N::inner_circuit_id(),
            transition.ciphertexts.clone(),
            transaction_proof,
        )
    }
}
