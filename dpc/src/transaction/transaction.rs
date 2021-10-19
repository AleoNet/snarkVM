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

use crate::{
    record::*,
    Address,
    AleoAmount,
    Event,
    Network,
    Request,
    Transition,
    Transitions,
    ViewKey,
    VirtualMachine,
};
use snarkvm_utilities::{
    has_duplicates,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashSet,
    hash::{Hash, Hasher},
};

#[derive(Derivative, Serialize, Deserialize)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Transaction<N: Network> {
    /// The ID of this transaction.
    transaction_id: N::TransactionID,
    /// The ID of the inner circuit used to execute each transition.
    inner_circuit_id: N::InnerCircuitID,
    /// The state transition.
    transitions: Vec<Transition<N>>,
    /// The events emitted from this transaction.
    events: Vec<Event<N>>,
}

impl<N: Network> Transaction<N> {
    /// Initializes a new transaction from a request.
    #[inline]
    pub fn new<R: Rng + CryptoRng>(request: &Request<N>, rng: &mut R) -> Result<Self> {
        VirtualMachine::<N>::new()?.execute(request, rng)?.finalize()
    }

    /// Initializes a new coinbase transaction.
    #[inline]
    pub fn new_coinbase<R: Rng + CryptoRng>(recipient: Address<N>, amount: AleoAmount, rng: &mut R) -> Result<Self> {
        let request = Request::new_coinbase(recipient, amount, rng)?;
        VirtualMachine::<N>::new()?.execute(&request, rng)?.finalize()
    }

    /// Initializes an instance of `Transaction` from the given inputs.
    #[inline]
    pub fn from(
        inner_circuit_id: N::InnerCircuitID,
        transitions: Vec<Transition<N>>,
        events: Vec<Event<N>>,
    ) -> Result<Self> {
        let transaction_id = Self::compute_transaction_id(&transitions)?;

        let transaction = Self {
            transaction_id,
            inner_circuit_id,
            transitions,
            events,
        };

        match transaction.is_valid() {
            true => Ok(transaction),
            false => Err(anyhow!("Failed to initialize a transaction")),
        }
    }

    /// Returns `true` if the transaction is well-formed, meaning it contains
    /// the correct network ID, unique serial numbers, unique commitments,
    /// correct ciphertext IDs, and a valid proof.
    #[inline]
    pub fn is_valid(&self) -> bool {
        // Ensure the number of transitions is between 1 and N::NUM_TRANSITIONS.
        let num_transitions = self.transitions.len();
        if num_transitions < 1 || num_transitions > N::NUM_TRANSITIONS as usize {
            eprintln!("Transaction contains invalid number of transitions");
            return false;
        }

        // Ensure the number of events is less than `N::NUM_EVENTS`.
        if self.events.len() > N::NUM_EVENTS as usize {
            eprintln!("Transaction contains an invalid number of events");
            return false;
        }

        // Returns `false` if the number of ledger roots in the transaction is incorrect.
        if self.ledger_roots().len() != num_transitions * N::NUM_INPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of ledger roots");
            return false;
        }

        // Returns `false` if the number of serial numbers in the transaction is incorrect.
        if self.serial_numbers().len() != num_transitions * N::NUM_INPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of serial numbers");
            return false;
        }

        // Returns `false` if there are duplicate serial numbers in the transaction.
        if has_duplicates(self.serial_numbers()) {
            eprintln!("Transaction contains duplicate serial numbers");
            return false;
        }

        // Returns `false` if the number of commitments in the transaction is incorrect.
        if self.commitments().len() != num_transitions * N::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of commitments");
            return false;
        }

        // Returns `false` if there are duplicate commitments numbers in the transaction.
        if has_duplicates(self.commitments()) {
            eprintln!("Transaction contains duplicate commitments");
            return false;
        }

        // Returns `false` if the number of record ciphertexts in the transaction is incorrect.
        if self.ciphertexts().len() != num_transitions * N::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of record ciphertexts");
            return false;
        }

        // Returns `false` if there are duplicate ciphertexts in the transition.
        if has_duplicates(self.ciphertexts()) {
            eprintln!("Transaction contains duplicate ciphertexts");
            return false;
        }

        // Initialize a local transitions tree.
        let mut transitions = match Transitions::<N>::new() {
            Ok(transitions) => transitions,
            Err(error) => {
                eprintln!("Transaction failed to initialize a local transitions tree: {}", error);
                return false;
            }
        };

        // Returns `false` if any transition is invalid.
        for transition in &self.transitions {
            // Returns `false` if the transition is invalid.
            if !transition.verify(self.inner_circuit_id, transitions.root()) {
                eprintln!("Transaction contains an invalid transition");
                return false;
            }

            // Update the local transitions tree.
            if let Err(error) = transitions.add(&transition) {
                eprintln!("Transaction failed to update local transitions tree: {}", error);
                return false;
            }
        }

        // Returns `false` if the size of the local commitments tree does not match the number of transitions.
        if transitions.len() != num_transitions {
            eprintln!("Transaction contains invalid local transitions tree state");
            return false;
        }

        // Returns `false` if the final transitions root does not match the transaction ID.
        if transitions.root() != self.transaction_id {
            eprintln!("Transaction contains an invalid transaction ID");
            return false;
        }

        true
    }

    /// Returns `true` if the given transition ID exists.
    pub fn contains_transition_id(&self, transition_id: &N::TransitionID) -> bool {
        self.transitions
            .iter()
            .map(Transition::transition_id)
            .contains(transition_id)
    }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &N::SerialNumber) -> bool {
        self.transitions
            .iter()
            .any(|t| (*t).contains_serial_number(serial_number))
    }

    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &N::Commitment) -> bool {
        self.transitions.iter().any(|t| (*t).contains_commitment(commitment))
    }

    /// Returns the transaction ID.
    #[inline]
    pub fn transaction_id(&self) -> N::TransactionID {
        self.transaction_id
    }

    /// Returns the inner circuit ID.
    #[inline]
    pub fn inner_circuit_id(&self) -> N::InnerCircuitID {
        self.inner_circuit_id
    }

    /// Returns the transition IDs.
    #[inline]
    pub fn transition_ids(&self) -> Vec<N::TransitionID> {
        self.transitions.iter().map(Transition::transition_id).collect()
    }

    /// Returns the ledger roots used to execute the transitions.
    #[inline]
    pub fn ledger_roots(&self) -> HashSet<N::LedgerRoot> {
        self.transitions
            .iter()
            .flat_map(Transition::ledger_roots)
            .cloned()
            .collect()
    }

    /// Returns the serial numbers.
    #[inline]
    pub fn serial_numbers(&self) -> Vec<N::SerialNumber> {
        self.transitions
            .iter()
            .flat_map(Transition::serial_numbers)
            .cloned()
            .collect()
    }

    /// Returns the commitments.
    #[inline]
    pub fn commitments(&self) -> Vec<N::Commitment> {
        self.transitions
            .iter()
            .flat_map(Transition::commitments)
            .cloned()
            .collect()
    }

    /// Returns the output record ciphertexts.
    #[inline]
    pub fn ciphertexts(&self) -> Vec<RecordCiphertext<N>> {
        self.transitions
            .iter()
            .flat_map(Transition::ciphertexts)
            .cloned()
            .collect()
    }

    /// Returns the value balance.
    #[inline]
    pub fn value_balance(&self) -> AleoAmount {
        self.transitions
            .iter()
            .map(Transition::value_balance)
            .fold(AleoAmount::ZERO, |a, b| a.add(*b))
    }

    /// Returns a reference to the state transitions.
    #[inline]
    pub fn transitions(&self) -> &Vec<Transition<N>> {
        &self.transitions
    }

    /// Returns a reference to the events.
    #[inline]
    pub fn events(&self) -> &Vec<Event<N>> {
        &self.events
    }

    /// Returns the ciphertext IDs.
    #[inline]
    pub fn to_ciphertext_ids(&self) -> Result<Vec<N::CiphertextID>> {
        self.transitions
            .iter()
            .flat_map(Transition::to_ciphertext_ids)
            .collect::<Result<Vec<_>>>()
    }

    /// Returns records from the transaction belonging to the given account view key.
    #[inline]
    pub fn to_decrypted_records(&self, account_view_key: &ViewKey<N>) -> Vec<Record<N>> {
        self.transitions
            .iter()
            .flat_map(Transition::ciphertexts)
            .filter_map(|c| c.decrypt(account_view_key).ok())
            .filter(|record| !record.is_dummy())
            .collect()
    }

    /// Transaction ID := MerkleTree(transition IDs)
    #[inline]
    pub(crate) fn compute_transaction_id(transitions: &Vec<Transition<N>>) -> Result<N::TransactionID> {
        // Initialize a transitions tree.
        let mut transitions_tree = Transitions::<N>::new()?;
        // Add all given transition IDs to the tree.
        transitions_tree.add_all(&transitions)?;
        // Return the root of the transitions tree.
        Ok(transitions_tree.root())
    }
}

impl<N: Network> FromBytes for Transaction<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let inner_circuit_id = FromBytes::read_le(&mut reader)?;

        let num_transitions: u16 = FromBytes::read_le(&mut reader)?;
        let mut transitions = Vec::with_capacity(num_transitions as usize);
        for _ in 0..num_transitions {
            transitions.push(FromBytes::read_le(&mut reader)?);
        }

        let num_events: u16 = FromBytes::read_le(&mut reader)?;
        let mut events = Vec::with_capacity(num_events as usize);
        for _ in 0..num_events {
            events.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self::from(inner_circuit_id, transitions, events).expect("Failed to deserialize a transaction"))
    }
}

impl<N: Network> ToBytes for Transaction<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.inner_circuit_id.write_le(&mut writer)?;
        (self.transitions.len() as u16).write_le(&mut writer)?;
        self.transitions.write_le(&mut writer)?;
        (self.events.len() as u16).write_le(&mut writer)?;
        self.events.write_le(&mut writer)
    }
}

impl<N: Network> Hash for Transaction<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.transaction_id.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet2::Testnet2, Account, AccountScheme};
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    #[test]
    fn test_decrypt_records() {
        let rng = &mut thread_rng();
        let account = Account::<Testnet2>::new(rng);

        // Craft the expected coinbase record.
        let expected_record = Record::new_output(
            account.address(),
            1234,
            Default::default(),
            *Testnet2::noop_program_id(),
            UniformRand::rand(rng),
            rng,
        )
        .unwrap();

        // Craft a transaction with 1 coinbase record.
        let transaction = Transaction::new_coinbase(account.address(), AleoAmount(1234), rng).unwrap();
        let decrypted_records = transaction.to_decrypted_records(&account.view_key());
        assert_eq!(decrypted_records.len(), 1); // Excludes dummy records upon decryption.

        let candidate_record = decrypted_records.first().unwrap();
        assert_eq!(expected_record.owner(), candidate_record.owner());
        assert_eq!(expected_record.value(), candidate_record.value());
        assert_eq!(expected_record.payload(), candidate_record.payload());
        assert_eq!(expected_record.program_id(), candidate_record.program_id());
    }
}
