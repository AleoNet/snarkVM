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
    circuits::{InputPublicVariables, OutputPublicVariables},
    prelude::*,
};
use snarkvm_algorithms::merkle_tree::{MerklePath, MerkleTree};
use snarkvm_utilities::{error, FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use serde::{de, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    hash::{Hash, Hasher},
    io::{Read, Result as IoResult, Write},
    str::FromStr,
    sync::Arc,
};

#[derive(Clone, Debug)]
pub struct Transition<N: Network> {
    /// The ID of this transition.
    transition_id: N::TransitionID,
    /// The serial numbers of the input records.
    serial_numbers: Vec<N::SerialNumber>,
    /// The commitments of the output records.
    commitments: Vec<N::Commitment>,
    /// The ciphertexts of the output records.
    ciphertexts: Vec<N::RecordCiphertext>,
    /// A value balance is the difference between the input and output record values.
    value_balance: AleoAmount,
    /// The commitments on the input record values.
    input_value_commitments: Vec<N::ValueCommitment>,
    /// The commitments on the output record values.
    output_value_commitments: Vec<N::ValueCommitment>,
    /// The value balance commitment.
    value_balance_commitment: N::ValueBalanceCommitment,
    /// The events emitted from this transition.
    events: Vec<Event<N>>,
    /// The zero-knowledge proofs attesting to the validity of this transition.
    execution: Execution<N>,
}

impl<N: Network> Transition<N> {
    /// Initializes a new instance of a transition.
    #[inline]
    pub(crate) fn new(request: &Request<N>, response: &Response<N>, execution: Execution<N>) -> Result<Self> {
        // Fetch the serial numbers.
        let serial_numbers = request.to_serial_numbers()?;

        // Fetch the ciphertexts and value balance.
        let transition_id = response.transition_id();
        let ciphertexts = response.ciphertexts();
        let value_balance = response.value_balance();
        let events = response.events().clone();

        let input_value_commitments = response.input_value_commitments().clone();
        let output_value_commitments = response.output_value_commitments().clone();
        let value_balance_commitment = response.value_balance_commitment().clone();

        // Construct the transition.
        Self::from(
            transition_id,
            serial_numbers,
            ciphertexts,
            value_balance,
            input_value_commitments,
            output_value_commitments,
            value_balance_commitment,
            events,
            execution,
        )
    }

    /// Constructs an instance of a transition from the given inputs.
    pub(crate) fn from(
        transition_id: N::TransitionID,
        serial_numbers: Vec<N::SerialNumber>,
        ciphertexts: Vec<N::RecordCiphertext>,
        value_balance: AleoAmount,
        input_value_commitments: Vec<N::ValueCommitment>,
        output_value_commitments: Vec<N::ValueCommitment>,
        value_balance_commitment: N::ValueBalanceCommitment,
        events: Vec<Event<N>>,
        execution: Execution<N>,
    ) -> Result<Self> {
        // Compute the commitments.
        let commitments = ciphertexts.iter().map(|c| c.commitment()).collect::<Vec<_>>();
        // Construct the transition.
        let transition = Self {
            transition_id: Self::compute_transition_id(&serial_numbers, &commitments)?,
            serial_numbers,
            commitments,
            ciphertexts,
            value_balance,
            input_value_commitments,
            output_value_commitments,
            value_balance_commitment,
            events,
            execution,
        };
        // Ensure the transition ID matches.
        match transition_id == transition.transition_id() {
            true => Ok(transition),
            false => Err(anyhow!(
                "Incorrect transition ID during deserialization. Expected {}, found {}",
                transition_id,
                transition.transition_id(),
            )),
        }
    }

    pub fn input_public_variables(
        &self,
        ledger_root: N::LedgerRoot,
        local_transitions_root: N::TransactionID,
    ) -> impl Iterator<Item = InputPublicVariables<N>> + '_ {
        let program_id = self.execution.program_execution.as_ref().map(|x| x.program_id);
        self.serial_numbers().zip_eq(self.input_value_commitments()).map(
            move |(serial_number, input_value_commitment)| {
                InputPublicVariables::new(
                    *serial_number,
                    input_value_commitment.clone(),
                    ledger_root,
                    local_transitions_root,
                    program_id,
                )
            },
        )
    }

    pub fn output_public_variables(&self) -> impl Iterator<Item = OutputPublicVariables<N>> + '_ {
        let program_id = self.execution.program_execution.as_ref().map(|x| x.program_id);
        self.commitments().zip_eq(self.output_value_commitments()).map(move |(commitment, output_value_commitment)| {
            OutputPublicVariables::new(*commitment, output_value_commitment.clone(), program_id)
        })
    }

    /// Returns `true` if the transition ID is well-formed and the transition proof is valid.
    #[inline]
    pub fn verify(
        &self,
        input_circuit_id: N::InputCircuitID,
        output_circuit_id: N::OutputCircuitID,
        ledger_root: N::LedgerRoot,
        local_transitions_root: N::TransactionID,
    ) -> bool {
        // Ensure the number of events is less than `N::NUM_EVENTS`.
        if self.events.len() > N::NUM_EVENTS as usize {
            eprintln!("Transition contains an invalid number of events");
            return false;
        }

        // Returns `false` if the input circuit ID does not match.
        if &input_circuit_id != N::input_circuit_id() {
            eprintln!("Invalid input circuit ID for network {}", N::NETWORK_ID);
            return false;
        }

        // Returns `false` if the output circuit ID does not match.
        if &output_circuit_id != N::output_circuit_id() {
            eprintln!("Invalid output circuit ID for network {}", N::NETWORK_ID);
            return false;
        }

        match self.transition_id.to_bytes_le() {
            Ok(message) => {
                // Verify that the value balance commitment is valid.
                match self.value_balance_commitment.verify(
                    &self.input_value_commitments,
                    &self.output_value_commitments,
                    self.value_balance,
                    &message,
                ) {
                    Ok(result) => {
                        if !result {
                            eprintln!("Transition contains an invalid value balance commitment");
                            return false;
                        }
                    }
                    Err(err) => {
                        eprintln!("Invalid value balance commitment verification {:?}", err);
                        return false;
                    }
                }
            }
            Err(err) => {
                eprintln!("Invalid transition id {}", err);
                return false;
            }
        }

        let program_id = self.execution.program_execution.as_ref().map(|x| x.program_id);

        let mut input_public_variables = Vec::with_capacity(N::NUM_INPUTS as usize);
        for (serial_number, input_value_commitment) in self.serial_numbers().zip_eq(self.input_value_commitments()) {
            let input_public = InputPublicVariables::<N>::new(
                *serial_number,
                input_value_commitment.clone(),
                ledger_root,
                local_transitions_root,
                program_id,
            );

            input_public_variables.push(input_public);
        }

        let mut output_public_variables = Vec::with_capacity(N::NUM_OUTPUTS as usize);
        for (commitment, output_value_commitment) in self.commitments().zip_eq(self.output_value_commitments()) {
            let output_public =
                OutputPublicVariables::<N>::new(*commitment, output_value_commitment.clone(), program_id);

            output_public_variables.push(output_public);
        }

        // Returns `false` if the execution is invalid.
        self.execution.verify(self.transition_id)
    }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &N::SerialNumber) -> bool {
        self.serial_numbers.contains(serial_number)
    }

    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &N::Commitment) -> bool {
        self.commitments.contains(commitment)
    }

    /// Returns the transition ID.
    #[inline]
    pub fn transition_id(&self) -> N::TransitionID {
        self.transition_id
    }

    /// Returns a reference to the serial numbers.
    #[inline]
    pub fn serial_numbers(&self) -> impl Iterator<Item = &N::SerialNumber> + fmt::Debug + '_ {
        self.serial_numbers.iter()
    }

    /// Returns a reference to the commitments.
    #[inline]
    pub fn commitments(&self) -> impl Iterator<Item = &N::Commitment> + fmt::Debug + '_ {
        self.commitments.iter()
    }

    /// Returns a reference to the ciphertexts.
    #[inline]
    pub fn ciphertexts(&self) -> impl Iterator<Item = &N::RecordCiphertext> + fmt::Debug + '_ {
        self.ciphertexts.iter()
    }

    /// Returns a reference to the value balance.
    #[inline]
    pub fn value_balance(&self) -> &AleoAmount {
        &self.value_balance
    }

    /// Returns a reference to the commitments on the input record values.
    pub fn input_value_commitments(&self) -> impl Iterator<Item = &N::ValueCommitment> + fmt::Debug + '_ {
        self.input_value_commitments.iter()
    }

    /// Returns a reference to the commitments on the output record values.
    pub fn output_value_commitments(&self) -> impl Iterator<Item = &N::ValueCommitment> + fmt::Debug + '_ {
        self.output_value_commitments.iter()
    }

    /// Returns a reference to the value balance commitment.
    pub fn value_balance_commitment(&self) -> &N::ValueBalanceCommitment {
        &self.value_balance_commitment
    }

    /// Returns a reference to the events.
    #[inline]
    pub fn events(&self) -> impl Iterator<Item = &Event<N>> + fmt::Debug + '_ {
        self.events.iter()
    }

    /// Returns a reference to the transition proofs.
    #[inline]
    pub fn execution(&self) -> &Execution<N> {
        &self.execution
    }

    /// Returns records from the transaction belonging to the given account view key.
    #[inline]
    pub fn to_decrypted_records<'a>(
        &'a self,
        decryption_key: &'a DecryptionKey<N>,
    ) -> impl Iterator<Item = Record<N>> + 'a {
        self.ciphertexts
            .iter()
            .filter_map(move |ciphertext| Record::<N>::decrypt(decryption_key, ciphertext).ok())
            .filter(|record| !record.is_dummy())
    }

    /// Returns the decrypted records using record view key events, if they exist.
    #[inline]
    pub fn to_records(&self) -> impl Iterator<Item = Record<N>> + fmt::Debug + '_ {
        let ciphertexts: Vec<&N::RecordCiphertext> = self.ciphertexts().collect();
        self.events
            .iter()
            .filter_map(move |event| match event {
                Event::RecordViewKey(i, record_view_key) => match ciphertexts.get(*i as usize) {
                    Some(ciphertext) => {
                        Record::decrypt(&DecryptionKey::from_record_view_key(record_view_key), *ciphertext).ok()
                    }
                    None => None,
                },
                _ => None,
            })
            .filter(|record| !record.is_dummy())
    }

    /// Returns an inclusion proof for the transition tree.
    #[inline]
    pub fn to_transition_inclusion_proof(&self, leaf: impl ToBytes) -> Result<MerklePath<N::TransitionIDParameters>> {
        // Convert the leaf into bytes.
        let leaf = leaf.to_bytes_le()?;

        // Retrieve the transition leaves.
        let leaves = Self::compute_transition_leaves(&self.serial_numbers, &self.commitments)?;

        // Find the index of the given leaf.
        for (index, candidate_leaf) in leaves.iter().enumerate() {
            if *candidate_leaf == leaf {
                let tree = MerkleTree::<N::TransitionIDParameters>::new(
                    Arc::new(N::transition_id_parameters().clone()),
                    &leaves,
                )?;
                return Ok(tree.generate_proof(index, &leaf)?);
            }
        }

        Err(anyhow!("Failed to find the given element in the transition"))
    }

    ///
    /// Returns the transition ID, which is the root of transition tree.
    ///
    #[inline]
    pub(crate) fn compute_transition_id(
        serial_numbers: &[N::SerialNumber],
        commitments: &[N::Commitment],
    ) -> Result<N::TransitionID> {
        let leaves = Self::compute_transition_leaves(serial_numbers, commitments)?;
        let tree =
            MerkleTree::<N::TransitionIDParameters>::new(Arc::new(N::transition_id_parameters().clone()), &leaves)?;
        Ok((*tree.root()).into())
    }

    ///
    /// Returns an instance of the transition tree.
    ///
    /// Transition Tree := MerkleTree(serial numbers || commitments)
    ///
    #[inline]
    pub(crate) fn compute_transition_leaves(
        serial_numbers: &[N::SerialNumber],
        commitments: &[N::Commitment],
    ) -> Result<Vec<Vec<u8>>> {
        // Construct the leaves of the transition tree.
        let leaves: Vec<Vec<u8>> = vec![
            // TODO (raychu86): split - handle padding serial numbers and commitments. (i.e. leaf 1 - 16 = serial numbers, 17 - 32 = commitments)
            serial_numbers.iter().take(N::NUM_INPUTS as usize).map(ToBytes::to_bytes_le).collect::<Result<Vec<_>>>()?,
            commitments.iter().take(N::NUM_OUTPUTS as usize).map(ToBytes::to_bytes_le).collect::<Result<Vec<_>>>()?,
        ]
        .concat();

        // Ensure the correct number of leaves are allocated.
        assert!(usize::pow(2, N::TRANSITION_TREE_DEPTH as u32) >= leaves.len());

        Ok(leaves)
    }
}

impl<N: Network> PartialEq for Transition<N> {
    fn eq(&self, other: &Self) -> bool {
        self.transition_id == other.transition_id
    }
}

impl<N: Network> Eq for Transition<N> {}

impl<N: Network> Hash for Transition<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.transition_id.hash(state);
    }
}

impl<N: Network> FromBytes for Transition<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let transition_id: N::TransitionID = FromBytes::read_le(&mut reader)?;

        let num_input_records: u16 = FromBytes::read_le(&mut reader)?;

        let mut serial_numbers = Vec::<N::SerialNumber>::with_capacity(num_input_records as usize);
        for _ in 0..num_input_records {
            serial_numbers.push(FromBytes::read_le(&mut reader)?);
        }

        let num_output_records: u16 = FromBytes::read_le(&mut reader)?;

        let mut ciphertexts = Vec::<N::RecordCiphertext>::with_capacity(num_output_records as usize);
        for _ in 0..num_output_records {
            ciphertexts.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance: AleoAmount = FromBytes::read_le(&mut reader)?;

        let mut input_value_commitments = Vec::with_capacity(num_input_records as usize);
        for _ in 0..num_input_records {
            input_value_commitments.push(FromBytes::read_le(&mut reader)?);
        }

        let mut output_value_commitments = Vec::with_capacity(num_output_records as usize);
        for _ in 0..num_output_records {
            output_value_commitments.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance_commitment = FromBytes::read_le(&mut reader)?;

        let num_events: u16 = FromBytes::read_le(&mut reader)?;
        let mut events = Vec::with_capacity(num_events as usize);
        for _ in 0..num_events {
            events.push(FromBytes::read_le(&mut reader)?);
        }

        let execution: Execution<N> = FromBytes::read_le(&mut reader)?;

        Self::from(
            transition_id,
            serial_numbers,
            ciphertexts,
            value_balance,
            input_value_commitments,
            output_value_commitments,
            value_balance_commitment,
            events,
            execution,
        )
        .map_err(|e| error(format!("Failed to deserialize a transition from bytes: {e}")))
    }
}

impl<N: Network> ToBytes for Transition<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.transition_id.write_le(&mut writer)?;

        // Ensure the number of serial numbers is within bounds.
        if self.serial_numbers.len() > N::NUM_INPUTS as usize {
            return Err(error(format!("The number of serial numbers cannot exceed {}", N::NUM_INPUTS)));
        }

        (self.serial_numbers.len() as u16).write_le(&mut writer)?;
        self.serial_numbers.write_le(&mut writer)?;

        // Ensure the number of ciphertexts is within bounds.
        if self.ciphertexts.len() > N::NUM_OUTPUTS as usize {
            return Err(error(format!("The number of ciphertexts cannot exceed {}", N::NUM_OUTPUTS)));
        }

        (self.ciphertexts.len() as u16).write_le(&mut writer)?;
        self.ciphertexts.write_le(&mut writer)?;

        self.value_balance.write_le(&mut writer)?;
        self.input_value_commitments.write_le(&mut writer)?;
        self.output_value_commitments.write_le(&mut writer)?;
        self.value_balance_commitment.write_le(&mut writer)?;

        // Ensure the number of events is within bounds.
        if self.events.len() > N::NUM_EVENTS as usize {
            return Err(error(format!("The number of events cannot exceed {}", N::NUM_EVENTS)));
        }

        (self.events.len() as u16).write_le(&mut writer)?;
        self.events.write_le(&mut writer)?;

        self.execution.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for Transition<N> {
    type Err = anyhow::Error;

    fn from_str(transition: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(transition)?)
    }
}

impl<N: Network> fmt::Display for Transition<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(serde::ser::Error::custom)?)
    }
}

impl<N: Network> Serialize for Transition<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut transition = serializer.serialize_struct("Transition", 10)?;
                transition.serialize_field("transition_id", &self.transition_id)?;
                transition.serialize_field("serial_numbers", &self.serial_numbers)?;
                transition.serialize_field("commitments", &self.commitments)?;
                transition.serialize_field("ciphertexts", &self.ciphertexts)?;
                transition.serialize_field("value_balance", &self.value_balance)?;
                transition.serialize_field("input_value_commitments", &self.input_value_commitments)?;
                transition.serialize_field("output_value_commitments", &self.output_value_commitments)?;
                transition.serialize_field("value_balance_commitment", &self.value_balance_commitment)?;
                transition.serialize_field("events", &self.events)?;
                transition.serialize_field("execution", &self.execution)?;
                transition.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Transition<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let transition = serde_json::Value::deserialize(deserializer)?;
                // Recover the transition.
                Self::from(
                    serde_json::from_value(transition["transition_id"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(transition["serial_numbers"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(transition["ciphertexts"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(transition["value_balance"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(transition["input_value_commitments"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(transition["output_value_commitments"].clone())
                        .map_err(de::Error::custom)?,
                    serde_json::from_value(transition["value_balance_commitment"].clone())
                        .map_err(de::Error::custom)?,
                    serde_json::from_value(transition["events"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(transition["execution"].clone()).map_err(de::Error::custom)?,
                )
                .map_err(de::Error::custom)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transition"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;

    #[test]
    fn test_size() {
        {
            use crate::testnet1::Testnet1;
            let transaction = Testnet1::genesis_block().to_coinbase_transaction().unwrap();
            let transition = transaction.transitions().first().unwrap().clone();
            let transition_bytes = transition.to_bytes_le().unwrap();
            assert_eq!(501, transition_bytes.len());
        }
        {
            let transaction = Testnet2::genesis_block().to_coinbase_transaction().unwrap();
            let transition = transaction.transitions().first().unwrap().clone();
            let transition_bytes = transition.to_bytes_le().unwrap();
            assert_eq!(501, transition_bytes.len());
        }
    }

    #[test]
    fn test_transition_serde_json() {
        let transaction = Testnet2::genesis_block().to_coinbase_transaction().unwrap();
        let expected_transition = transaction.transitions().first().unwrap().clone();

        // Serialize
        let expected_string = expected_transition.to_string();
        let candidate_string = serde_json::to_string(&expected_transition).unwrap();
        assert_eq!(1185, candidate_string.len(), "Update me if serialization has changed");
        assert_eq!(expected_string, candidate_string);

        // Deserialize
        assert_eq!(expected_transition, Transition::from_str(&candidate_string).unwrap());
        assert_eq!(expected_transition, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_transition_bincode() {
        let transaction = Testnet2::genesis_block().to_coinbase_transaction().unwrap();
        let expected_transition = transaction.transitions().first().unwrap().clone();

        // Serialize
        let expected_bytes = expected_transition.to_bytes_le().unwrap();
        let candidate_bytes = bincode::serialize(&expected_transition).unwrap();
        assert_eq!(501, expected_bytes.len(), "Update me if serialization has changed");
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

        // Deserialize
        assert_eq!(expected_transition, Transition::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_transition, bincode::deserialize(&candidate_bytes[..]).unwrap());
    }
}
