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

use crate::{circuits::*, prelude::*};
use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTree},
    traits::SNARK,
};
use snarkvm_utilities::{FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::{anyhow, Result};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    hash::{Hash, Hasher},
    io::{Read, Result as IoResult, Write},
    str::FromStr,
    sync::Arc,
};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
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
    /// The zero-knowledge proof attesting to the validity of this transition.
    proof: N::OuterProof,
}

impl<N: Network> Transition<N> {
    /// Initializes a new instance of a transition.
    #[inline]
    pub(crate) fn new(request: &Request<N>, response: &Response<N>, proof: N::OuterProof) -> Result<Self> {
        // Fetch the serial numbers.
        let serial_numbers = request.to_serial_numbers()?;

        // Fetch the commitments and ciphertexts.
        let commitments = response.commitments();
        let ciphertexts = response.ciphertexts().clone();
        let value_balance = response.value_balance();

        // Construct the transition.
        Self::from(serial_numbers, commitments, ciphertexts, value_balance, proof)
    }

    /// Constructs an instance of a transition from the given inputs.
    pub(crate) fn from(
        serial_numbers: Vec<N::SerialNumber>,
        commitments: Vec<N::Commitment>,
        ciphertexts: Vec<N::RecordCiphertext>,
        value_balance: AleoAmount,
        proof: N::OuterProof,
    ) -> Result<Self> {
        // Compute the transition ID.
        let transition_id = Self::compute_transition_id(&serial_numbers, &commitments, &ciphertexts, value_balance)?;

        // Construct the transition.
        Ok(Self {
            transition_id,
            serial_numbers,
            commitments,
            ciphertexts,
            value_balance,
            proof,
        })
    }

    /// Returns `true` if the transition ID is well-formed and the transition proof is valid.
    #[inline]
    pub fn verify(
        &self,
        inner_circuit_id: N::InnerCircuitID,
        ledger_root: N::LedgerRoot,
        local_transitions_root: N::TransactionID,
    ) -> bool {
        // Returns `false` if the transition ID does not match the computed one.
        match Self::compute_transition_id(
            &self.serial_numbers,
            &self.commitments,
            &self.ciphertexts,
            self.value_balance,
        ) {
            Ok(computed_transition_id) => {
                if computed_transition_id != self.transition_id {
                    eprintln!(
                        "Transition ID is incorrect. Expected {}, found {}",
                        computed_transition_id, self.transition_id
                    );
                    return false;
                }
            }
            Err(error) => {
                eprintln!("Failed to compute the transition ID for verification: {}", error);
                return false;
            }
        };

        // Returns `false` if the transition proof is invalid.
        match N::OuterSNARK::verify(
            N::outer_verifying_key(),
            &OuterPublicVariables::new(
                self.transition_id,
                ledger_root,
                local_transitions_root,
                inner_circuit_id,
            ),
            &self.proof,
        ) {
            Ok(is_valid) => match is_valid {
                true => true,
                false => {
                    eprintln!("Transition proof failed to verify");
                    return false;
                }
            },
            Err(error) => {
                eprintln!("Failed to validate transition proof: {:?}", error);
                return false;
            }
        }
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
    pub fn serial_numbers(&self) -> &Vec<N::SerialNumber> {
        &self.serial_numbers
    }

    /// Returns a reference to the commitments.
    #[inline]
    pub fn commitments(&self) -> &Vec<N::Commitment> {
        &self.commitments
    }

    /// Returns the ciphertext IDs.
    #[inline]
    pub fn ciphertext_ids(&self) -> impl Iterator<Item = N::CiphertextID> + fmt::Debug + '_ {
        self.ciphertexts.iter().map(|c| (*c).ciphertext_id())
    }

    /// Returns a reference to the ciphertexts.
    #[inline]
    pub fn ciphertexts(&self) -> &Vec<N::RecordCiphertext> {
        &self.ciphertexts
    }

    /// Returns a reference to the value balance.
    #[inline]
    pub fn value_balance(&self) -> &AleoAmount {
        &self.value_balance
    }

    /// Returns a reference to the transition proof.
    #[inline]
    pub fn proof(&self) -> &N::OuterProof {
        &self.proof
    }

    /// Returns an inclusion proof for the transition tree.
    #[inline]
    pub fn to_transition_inclusion_proof(&self, leaf: impl ToBytes) -> Result<MerklePath<N::TransitionIDParameters>> {
        // Convert the leaf into bytes.
        let leaf = leaf.to_bytes_le()?;

        // Retrieve the transition leaves.
        let leaves = Self::compute_transition_leaves(
            &self.serial_numbers,
            &self.commitments,
            &self.ciphertexts,
            self.value_balance,
        )?;

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
        serial_numbers: &Vec<N::SerialNumber>,
        commitments: &Vec<N::Commitment>,
        ciphertexts: &Vec<N::RecordCiphertext>,
        value_balance: AleoAmount,
    ) -> Result<N::TransitionID> {
        let leaves = Self::compute_transition_leaves(serial_numbers, commitments, ciphertexts, value_balance)?;
        let tree =
            MerkleTree::<N::TransitionIDParameters>::new(Arc::new(N::transition_id_parameters().clone()), &leaves)?;
        Ok((*tree.root()).into())
    }

    ///
    /// Returns an instance of the transition tree.
    ///
    /// Transition Tree := MerkleTree(serial numbers || commitments || ciphertext_ids || value balance)
    ///
    #[inline]
    pub(crate) fn compute_transition_leaves(
        serial_numbers: &Vec<N::SerialNumber>,
        commitments: &Vec<N::Commitment>,
        ciphertexts: &Vec<N::RecordCiphertext>,
        value_balance: AleoAmount,
    ) -> Result<Vec<Vec<u8>>> {
        // Construct the leaves of the transition tree.
        let leaves: Vec<Vec<u8>> = vec![
            // Leaf 0, 1 := serial numbers
            serial_numbers
                .iter()
                .take(N::NUM_INPUT_RECORDS)
                .map(ToBytes::to_bytes_le)
                .collect::<Result<Vec<_>>>()?,
            // Leaf 2, 3 := commitments
            commitments
                .iter()
                .take(N::NUM_OUTPUT_RECORDS)
                .map(ToBytes::to_bytes_le)
                .collect::<Result<Vec<_>>>()?,
            // Leaf 4, 5 := ciphertext IDs
            ciphertexts
                .iter()
                .take(N::NUM_OUTPUT_RECORDS)
                .map(|c| Ok(c.ciphertext_id().to_bytes_le()?))
                .collect::<Result<Vec<_>>>()?,
            // Leaf 6 := value balance
            vec![value_balance.to_bytes_le()?],
            // Leaf 7 := unallocated
            vec![vec![0u8; 32]],
        ]
        .concat();

        // Ensure the correct number of leaves are allocated.
        assert_eq!(usize::pow(2, N::TRANSITION_TREE_DEPTH as u32), leaves.len());

        Ok(leaves)
    }
}

impl<N: Network> FromBytes for Transition<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut serial_numbers = Vec::<N::SerialNumber>::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            serial_numbers.push(FromBytes::read_le(&mut reader)?);
        }

        let mut commitments = Vec::<N::Commitment>::with_capacity(N::NUM_OUTPUT_RECORDS);
        for _ in 0..N::NUM_OUTPUT_RECORDS {
            commitments.push(FromBytes::read_le(&mut reader)?);
        }

        let mut ciphertexts = Vec::<N::RecordCiphertext>::with_capacity(N::NUM_OUTPUT_RECORDS);
        for _ in 0..N::NUM_OUTPUT_RECORDS {
            ciphertexts.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance: AleoAmount = FromBytes::read_le(&mut reader)?;
        let proof: N::OuterProof = FromBytes::read_le(&mut reader)?;

        Ok(
            Self::from(serial_numbers, commitments, ciphertexts, value_balance, proof)
                .expect("Failed to deserialize a transition from bytes"),
        )
    }
}

impl<N: Network> ToBytes for Transition<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.serial_numbers.write_le(&mut writer)?;
        self.commitments.write_le(&mut writer)?;
        self.ciphertexts.write_le(&mut writer)?;
        self.value_balance.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for Transition<N> {
    type Err = anyhow::Error;

    fn from_str(transition: &str) -> Result<Self, Self::Err> {
        let transition = serde_json::Value::from_str(transition)?;
        let transition_id: N::TransitionID = serde_json::from_value(transition["transition_id"].clone())?;

        // Recover the transition.
        let transition = Self::from(
            serde_json::from_value(transition["serial_numbers"].clone())?,
            serde_json::from_value(transition["commitments"].clone())?,
            serde_json::from_value(transition["ciphertexts"].clone())?,
            serde_json::from_value(transition["value_balance"].clone())?,
            serde_json::from_value(transition["proof"].clone())?,
        )?;

        // Ensure the transition ID matches.
        match transition_id == transition.transition_id() {
            true => Ok(transition),
            false => Err(anyhow!(
                "Incorrect transition ID during deserialization. Expected {}, found {}",
                transition_id,
                transition.transition_id()
            )),
        }
    }
}

impl<N: Network> fmt::Display for Transition<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let transition = serde_json::json!({
           "transition_id": self.transition_id,
           "serial_numbers": self.serial_numbers,
           "commitments": self.commitments,
           "ciphertext_ids": self.ciphertext_ids().collect::<Vec<_>>(),
           "ciphertexts": self.ciphertexts,
           "value_balance": self.value_balance,
           "proof": self.proof,
        });
        write!(f, "{}", transition)
    }
}

impl<N: Network> Serialize for Transition<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Transition<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => {
                FromBytesDeserializer::<Self>::deserialize(deserializer, "transition", N::TRANSITION_SIZE_IN_BYTES)
            }
        }
    }
}

impl<N: Network> Hash for Transition<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.transition_id.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;

    #[test]
    fn test_size() {
        let transaction = Testnet2::genesis_block().to_coinbase_transaction().unwrap();
        let transition = transaction.transitions().first().unwrap().clone();
        assert_eq!(
            Testnet2::TRANSITION_SIZE_IN_BYTES,
            transition.to_bytes_le().unwrap().len(),
        );
    }

    #[test]
    fn test_serde_json() {
        let transaction = Testnet2::genesis_block().to_coinbase_transaction().unwrap();
        let expected_transition = transaction.transitions().first().unwrap().clone();

        // Serialize
        let expected_string = &expected_transition.to_string();
        let candidate_string = serde_json::to_string(&expected_transition).unwrap();
        assert_eq!(2372, candidate_string.len(), "Update me if serialization has changed");
        assert_eq!(
            expected_string,
            serde_json::Value::from_str(&candidate_string)
                .unwrap()
                .as_str()
                .unwrap()
        );

        // Deserialize
        assert_eq!(expected_transition, Transition::from_str(&expected_string).unwrap());
        assert_eq!(expected_transition, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_bincode() {
        let transaction = Testnet2::genesis_block().to_coinbase_transaction().unwrap();
        let expected_transition = transaction.transitions().first().unwrap().clone();

        println!("{}", serde_json::to_string(&expected_transition).unwrap());

        let expected_bytes = expected_transition.to_bytes_le().unwrap();
        assert_eq!(
            &expected_bytes[..],
            &bincode::serialize(&expected_transition).unwrap()[..]
        );

        assert_eq!(expected_transition, Transition::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected_transition, bincode::deserialize(&expected_bytes[..]).unwrap());
    }
}
