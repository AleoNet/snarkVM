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

use crate::{
    record::*,
    Address,
    Amount,
    Event,
    LedgerTree,
    LedgerTreeScheme,
    LocalProof,
    Network,
    Request,
    Transition,
    Transitions,
    VirtualMachine,
};
use snarkvm_utilities::{
    has_duplicates,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
};

use anyhow::{anyhow, Result};
use core::{
    fmt,
    hash::{Hash, Hasher},
    str::FromStr,
};
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use serde::{de, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};

#[derive(Clone, Debug)]
pub struct Transaction<N: Network> {
    /// The ID of this transaction.
    transaction_id: N::TransactionID,
    /// The ID of the inner circuit used to execute each transition.
    inner_circuit_id: N::InnerCircuitID,
    /// The ledger root used to prove inclusion of ledger-consumed records.
    ledger_root: N::LedgerRoot,
    /// The state transition.
    transitions: Vec<Transition<N>>,
}

impl<N: Network> Transaction<N> {
    /// Initializes a new transaction from a request.
    #[inline]
    pub fn new<R: Rng + CryptoRng>(ledger: LedgerTree<N>, request: &Request<N>, rng: &mut R) -> Result<Self> {
        let (vm, _) = VirtualMachine::<N>::new(ledger.root())?.execute(request, rng)?;
        vm.finalize()
    }

    /// Initializes a new coinbase transaction.
    #[inline]
    pub fn new_coinbase<R: Rng + CryptoRng>(
        recipient: Address<N>,
        amount: Amount,
        is_public: bool,
        rng: &mut R,
    ) -> Result<(Self, Record<N>)> {
        let request = Request::new_coinbase(recipient, amount, is_public, rng)?;
        let (vm, response) = VirtualMachine::<N>::new(LedgerTree::<N>::new()?.root())?.execute(&request, rng)?;
        Ok((vm.finalize()?, response.records()[0].clone()))
    }

    /// Initializes an instance of `Transaction` from the given inputs.
    #[inline]
    pub fn from(
        inner_circuit_id: N::InnerCircuitID,
        ledger_root: N::LedgerRoot,
        transitions: Vec<Transition<N>>,
    ) -> Result<Self> {
        let transaction_id = Self::compute_transaction_id(&transitions)?;

        let transaction = Self { transaction_id, inner_circuit_id, ledger_root, transitions };

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
        if self.events().count() > num_transitions * N::NUM_EVENTS as usize {
            eprintln!("Transaction contains an invalid number of events");
            return false;
        }

        // Returns `false` if the number of serial numbers in the transaction is incorrect.
        if self.serial_numbers().count() != num_transitions * N::NUM_INPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of serial numbers");
            return false;
        }

        // Returns `false` if there are duplicate serial numbers in the transaction.
        if has_duplicates(self.serial_numbers()) {
            eprintln!("Transaction contains duplicate serial numbers");
            return false;
        }

        // Returns `false` if the number of commitments in the transaction is incorrect.
        if self.commitments().count() != num_transitions * N::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of commitments");
            return false;
        }

        // Returns `false` if there are duplicate commitments numbers in the transaction.
        if has_duplicates(self.commitments()) {
            eprintln!("Transaction contains duplicate commitments");
            return false;
        }

        // Returns `false` if the number of record ciphertexts in the transaction is incorrect.
        if self.ciphertexts().count() != num_transitions * N::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of record ciphertexts");
            return false;
        }

        // Returns `false` if there are duplicate ciphertexts in the transition.
        if has_duplicates(self.ciphertexts()) {
            eprintln!("Transaction contains duplicate ciphertexts");
            return false;
        }

        // Returns `false` if the transaction is not a coinbase, and has a transition with a negative value balance.
        if self.transitions.len() > 1
            && self.transitions.iter().any(|transition| transition.value_balance().is_negative())
        {
            eprintln!("Transaction contains a transition with a negative value balance");
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
            if !transition.verify(self.inner_circuit_id, self.ledger_root, transitions.root()) {
                eprintln!("Transaction contains an invalid transition");
                return false;
            }

            // Update the local transitions tree.
            if let Err(error) = transitions.add(transition) {
                eprintln!("Transaction failed to update local transitions tree: {}", error);
                return false;
            }
        }

        // Returns `false` if the size of the local transitions tree does not match the number of transitions.
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
        self.transitions.iter().map(Transition::transition_id).contains(transition_id)
    }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &N::SerialNumber) -> bool {
        self.transitions.iter().any(|t| (*t).contains_serial_number(serial_number))
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

    /// Returns the ledger root used to execute the transitions.
    #[inline]
    pub fn ledger_root(&self) -> N::LedgerRoot {
        self.ledger_root
    }

    /// Returns the transition IDs.
    #[inline]
    pub fn transition_ids(&self) -> impl Iterator<Item = N::TransitionID> + fmt::Debug + '_ {
        self.transitions.iter().map(Transition::transition_id)
    }

    /// Returns the serial numbers.
    #[inline]
    pub fn serial_numbers(&self) -> impl Iterator<Item = &N::SerialNumber> + fmt::Debug + '_ {
        self.transitions.iter().flat_map(Transition::serial_numbers)
    }

    /// Returns the commitments.
    #[inline]
    pub fn commitments(&self) -> impl Iterator<Item = &N::Commitment> + fmt::Debug + '_ {
        self.transitions.iter().flat_map(Transition::commitments)
    }

    /// Returns the output record ciphertexts.
    #[inline]
    pub fn ciphertexts(&self) -> impl Iterator<Item = &N::RecordCiphertext> + fmt::Debug + '_ {
        self.transitions.iter().flat_map(Transition::ciphertexts)
    }

    /// Returns the value balance.
    #[inline]
    pub fn value_balance(&self) -> Amount {
        self.transitions.iter().map(Transition::value_balance).fold(Amount::ZERO, |a, b| a + *b)
    }

    /// Returns the events.
    #[inline]
    pub fn events(&self) -> impl Iterator<Item = &Event<N>> + fmt::Debug + '_ {
        self.transitions.iter().flat_map(Transition::events)
    }

    /// Returns a reference to the state transitions.
    #[inline]
    pub fn transitions(&self) -> &Vec<Transition<N>> {
        &self.transitions
    }

    /// Returns records from the transaction belonging to the given account view key.
    #[inline]
    pub fn to_decrypted_records<'a>(
        &'a self,
        decryption_key: &'a DecryptionKey<N>,
    ) -> impl Iterator<Item = Record<N>> + 'a {
        self.transitions.iter().flat_map(move |transition| transition.to_decrypted_records(decryption_key))
    }

    /// Returns the decrypted records using record view key events, if they exist.
    #[inline]
    pub fn to_records(&self) -> impl Iterator<Item = Record<N>> + fmt::Debug + '_ {
        self.transitions.iter().flat_map(Transition::to_records)
    }

    /// Returns the local proof for a given commitment.
    #[inline]
    pub fn to_local_proof(&self, record_commitment: N::Commitment) -> Result<LocalProof<N>> {
        // Initialize a transitions tree.
        let mut transitions_tree = Transitions::<N>::new()?;
        // Add all given transition IDs to the tree.
        transitions_tree.add_all(self.transitions())?;
        // Return the local proof for the transitions tree.
        transitions_tree.to_local_proof(record_commitment)
    }

    /// Transaction ID := MerkleTree(transition IDs)
    #[inline]
    pub(crate) fn compute_transaction_id(transitions: &[Transition<N>]) -> Result<N::TransactionID> {
        // Initialize a transitions tree.
        let mut transitions_tree = Transitions::<N>::new()?;
        // Add all given transition IDs to the tree.
        transitions_tree.add_all(transitions)?;
        // Return the root of the transitions tree.
        Ok(transitions_tree.root())
    }
}

impl<N: Network> PartialEq for Transaction<N> {
    fn eq(&self, other: &Self) -> bool {
        self.transaction_id == other.transaction_id
    }
}

impl<N: Network> Eq for Transaction<N> {}

impl<N: Network> Hash for Transaction<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.transaction_id.hash(state);
    }
}

impl<N: Network> FromBytes for Transaction<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let inner_circuit_id = FromBytes::read_le(&mut reader)?;
        let ledger_root = FromBytes::read_le(&mut reader)?;

        let num_transitions: u16 = FromBytes::read_le(&mut reader)?;
        let mut transitions = Vec::with_capacity(num_transitions as usize);
        for _ in 0..num_transitions {
            transitions.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self::from(inner_circuit_id, ledger_root, transitions).expect("Failed to deserialize a transaction"))
    }
}

impl<N: Network> ToBytes for Transaction<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.inner_circuit_id.write_le(&mut writer)?;
        self.ledger_root.write_le(&mut writer)?;
        (self.transitions.len() as u16).write_le(&mut writer)?;
        self.transitions.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for Transaction<N> {
    type Err = anyhow::Error;

    fn from_str(transaction: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(transaction)?)
    }
}

impl<N: Network> fmt::Display for Transaction<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(serde::ser::Error::custom)?)
    }
}

impl<N: Network> Serialize for Transaction<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut transaction = serializer.serialize_struct("Transaction", 5)?;
                transaction.serialize_field("transaction_id", &self.transaction_id)?;
                transaction.serialize_field("inner_circuit_id", &self.inner_circuit_id)?;
                transaction.serialize_field("ledger_root", &self.ledger_root)?;
                transaction.serialize_field("transitions", &self.transitions)?;
                transaction.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Transaction<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let transaction = serde_json::Value::deserialize(deserializer)?;
                let transaction_id =
                    N::TransactionID::deserialize(transaction["transaction_id"].clone()).map_err(de::Error::custom)?;

                // Recover the transaction.
                let transaction = Self::from(
                    serde_json::from_value(transaction["inner_circuit_id"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(transaction["ledger_root"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(transaction["transitions"].clone()).map_err(de::Error::custom)?,
                )
                .map_err(de::Error::custom)?;

                // Ensure the transaction ID matches.
                match transaction_id == transaction.transaction_id() {
                    true => Ok(transaction),
                    false => Err(anyhow!(
                        "Incorrect transaction ID during deserialization. Expected {}, found {}",
                        transaction.transaction_id(),
                        transaction_id
                    ))
                    .map_err(de::Error::custom),
                }
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transaction"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet2::Testnet2, Account};

    use rand::thread_rng;

    #[test]
    fn test_decrypt_records() {
        let rng = &mut thread_rng();
        let account = Account::<Testnet2>::new(rng);

        // Craft a transaction with 1 coinbase record.
        let (transaction, expected_record) =
            Transaction::new_coinbase(account.address(), Amount(1234), true, rng).unwrap();
        let decrypted_records =
            transaction.to_decrypted_records(&account.view_key().into()).collect::<Vec<Record<Testnet2>>>();
        assert_eq!(decrypted_records.len(), 1); // Excludes dummy records upon decryption.

        let candidate_record = decrypted_records.first().unwrap();
        assert_eq!(&expected_record, candidate_record);
        assert_eq!(expected_record.owner(), candidate_record.owner());
        assert_eq!(expected_record.value(), candidate_record.value());
        // TODO (howardwu): Reenable this after fixing how payloads are handled.
        // assert_eq!(expected_record.payload(), candidate_record.payload());
        assert_eq!(expected_record.program_id(), candidate_record.program_id());
    }

    #[test]
    fn test_public_coinbase_record() {
        let rng = &mut thread_rng();
        let account = Account::<Testnet2>::new(rng);

        // Craft a transaction with 1 coinbase record.
        let (transaction, expected_record) =
            Transaction::new_coinbase(account.address(), Amount(1234), true, rng).unwrap();

        let public_records = transaction.to_records().collect::<Vec<_>>();
        assert_eq!(public_records.len(), 2);
        // TODO (howardwu): Reenable this after fixing how payloads are handled.
        // assert_eq!(public_records.len(), 1); // Excludes dummy records upon decryption.

        let candidate_record = public_records.first().unwrap();
        assert_eq!(&expected_record, candidate_record);
        assert_eq!(expected_record.owner(), candidate_record.owner());
        assert_eq!(expected_record.value(), candidate_record.value());
        // TODO (howardwu): Reenable this after fixing how payloads are handled.
        // assert_eq!(expected_record.payload(), candidate_record.payload());
        assert_eq!(expected_record.program_id(), candidate_record.program_id());
    }

    #[test]
    fn test_transaction_serde_json() {
        let rng = &mut thread_rng();
        let account = Account::<Testnet2>::new(rng);

        // Craft a transaction with 1 coinbase record.
        let (expected_transaction, _) =
            Transaction::<Testnet2>::new_coinbase(account.address(), Amount(1234), true, rng).unwrap();

        // Serialize
        let expected_string = expected_transaction.to_string();
        let candidate_string = serde_json::to_string(&expected_transaction).unwrap();
        assert_eq!(2258, candidate_string.len(), "Update me if serialization has changed");
        assert_eq!(expected_string, candidate_string);

        // Deserialize
        assert_eq!(expected_transaction, Transaction::from_str(&candidate_string).unwrap());
        assert_eq!(expected_transaction, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_transaction_bincode() {
        let rng = &mut thread_rng();
        let account = Account::<Testnet2>::new(rng);

        // Craft a transaction with 1 coinbase record.
        let (expected_transaction, _) =
            Transaction::<Testnet2>::new_coinbase(account.address(), Amount(1234), true, rng).unwrap();

        // Serialize
        let expected_bytes = expected_transaction.to_bytes_le().unwrap();
        let candidate_bytes = bincode::serialize(&expected_transaction).unwrap();
        assert_eq!(1038, expected_bytes.len(), "Update me if serialization has changed");
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

        // Deserialize
        assert_eq!(expected_transaction, Transaction::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_transaction, bincode::deserialize(&candidate_bytes[..]).unwrap());
    }
}
