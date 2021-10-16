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
use snarkvm_algorithms::traits::{CRH, SNARK};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
};

#[derive(Derivative, Serialize, Deserialize)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Transition<N: Network> {
    /// The ID of this transition.
    transition_id: N::TransitionID,
    /// The block hash used to prove inclusion of ledger-consumed records.
    block_hash: N::BlockHash,
    /// The local commitments root used to prove inclusion of locally-consumed records.
    local_commitments_root: N::LocalCommitmentsRoot,
    /// The serial numbers of the input records.
    serial_numbers: Vec<N::SerialNumber>,
    /// The commitments of the output records.
    commitments: Vec<N::Commitment>,
    /// The ciphertexts of the output records.
    ciphertexts: Vec<RecordCiphertext<N>>,
    /// A value balance is the difference between the input and output record values.
    value_balance: AleoAmount,
    /// The events emitted from this transition.
    events: Vec<Event<N>>,
    /// The zero-knowledge proof attesting to the validity of this transition.
    proof: N::OuterProof,
}

impl<N: Network> Transition<N> {
    /// Initializes a new instance of a transition.
    #[inline]
    pub(crate) fn from(request: &Request<N>, response: &Response<N>, proof: N::OuterProof) -> Result<Self> {
        // Fetch the block hash, local commitments root, and serial numbers.
        let block_hash = request.block_hash();
        let local_commitments_root = request.local_commitments_root();
        let serial_numbers = request.to_serial_numbers()?;

        // Fetch the commitments and ciphertexts.
        let commitments = response.commitments();
        let ciphertexts = response.ciphertexts().clone();
        let value_balance = response.value_balance();
        let events = response.events().clone();

        // Compute the transition ID.
        let transition_id = Self::compute_transition_id(
            block_hash,
            local_commitments_root,
            &serial_numbers,
            &commitments,
            &ciphertexts,
            value_balance,
        )?;

        // Construct the transition.
        Ok(Self {
            transition_id,
            block_hash,
            local_commitments_root,
            serial_numbers,
            commitments,
            ciphertexts,
            value_balance,
            events,
            proof,
        })
    }

    /// Returns `true` if the transition proof is valid, and the local commitments root matches.
    #[inline]
    pub fn verify(&self, inner_circuit_id: N::InnerCircuitID, local_commitments_root: N::LocalCommitmentsRoot) -> bool {
        // Returns `false` if the local commitments root does not match the given one.
        if self.local_commitments_root != local_commitments_root {
            eprintln!(
                "Transition contains incorrect local commitments root: {} != {}",
                self.local_commitments_root, local_commitments_root
            );
            return false;
        }

        // Returns `false` if the transition ID does not match the computed one.
        match Self::compute_transition_id(
            self.block_hash,
            self.local_commitments_root,
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
            &OuterPublicVariables::new(self.transition_id, inner_circuit_id),
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

    /// Returns the transition ID.
    #[inline]
    pub fn transition_id(&self) -> N::TransitionID {
        self.transition_id
    }

    /// Returns the block hash used to prove inclusion of ledger-consumed records.
    #[inline]
    pub fn block_hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the local commitments root used to prove inclusion of locally-consumed records.
    #[inline]
    pub fn local_commitments_root(&self) -> N::LocalCommitmentsRoot {
        self.local_commitments_root
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

    /// Returns a reference to the ciphertexts.
    #[inline]
    pub fn ciphertexts(&self) -> &Vec<RecordCiphertext<N>> {
        &self.ciphertexts
    }

    /// Returns a reference to the value balance.
    #[inline]
    pub fn value_balance(&self) -> &AleoAmount {
        &self.value_balance
    }

    /// Returns a reference to the events.
    #[inline]
    pub fn events(&self) -> &Vec<Event<N>> {
        &self.events
    }

    /// Returns a reference to the transition proof.
    #[inline]
    pub fn proof(&self) -> &N::OuterProof {
        &self.proof
    }

    /// Returns the ciphertext IDs.
    #[inline]
    pub fn to_ciphertext_ids(&self) -> impl Iterator<Item = Result<N::CiphertextID>> + fmt::Debug + '_ {
        self.ciphertexts.iter().map(RecordCiphertext::to_ciphertext_id)
    }

    /// Transition ID := Hash(block hash || local commitments root || serial numbers || commitments || ciphertext_ids || value balance)
    #[inline]
    pub(crate) fn compute_transition_id(
        block_hash: N::BlockHash,
        local_commitments_root: N::LocalCommitmentsRoot,
        serial_numbers: &Vec<N::SerialNumber>,
        commitments: &Vec<N::Commitment>,
        ciphertexts: &Vec<RecordCiphertext<N>>,
        value_balance: AleoAmount,
    ) -> Result<N::TransitionID> {
        Ok(N::transition_id_crh().hash(&to_bytes_le![
            block_hash,
            local_commitments_root,
            serial_numbers,
            commitments,
            ciphertexts
                .iter()
                .map(RecordCiphertext::to_ciphertext_id)
                .collect::<Result<Vec<_>>>()?,
            value_balance
        ]?)?)
    }
}

impl<N: Network> FromBytes for Transition<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let block_hash = FromBytes::read_le(&mut reader)?;
        let local_commitments_root = FromBytes::read_le(&mut reader)?;

        let mut serial_numbers = Vec::<N::SerialNumber>::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            serial_numbers.push(FromBytes::read_le(&mut reader)?);
        }

        let mut commitments = Vec::<N::Commitment>::with_capacity(N::NUM_OUTPUT_RECORDS);
        for _ in 0..N::NUM_OUTPUT_RECORDS {
            commitments.push(FromBytes::read_le(&mut reader)?);
        }

        let mut ciphertexts = Vec::<RecordCiphertext<N>>::with_capacity(N::NUM_OUTPUT_RECORDS);
        for _ in 0..N::NUM_OUTPUT_RECORDS {
            ciphertexts.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance: AleoAmount = FromBytes::read_le(&mut reader)?;

        let num_events: u16 = FromBytes::read_le(&mut reader)?;
        let mut events = Vec::with_capacity(num_events as usize);
        for _ in 0..num_events {
            events.push(FromBytes::read_le(&mut reader)?);
        }

        let proof: N::OuterProof = FromBytes::read_le(&mut reader)?;

        let transition_id = Self::compute_transition_id(
            block_hash,
            local_commitments_root,
            &serial_numbers,
            &commitments,
            &ciphertexts,
            value_balance,
        )
        .expect("Failed to compute the transition ID during deserialization");

        Ok(Self {
            transition_id,
            block_hash,
            local_commitments_root,
            serial_numbers,
            commitments,
            ciphertexts,
            value_balance,
            events,
            proof,
        })
    }
}

impl<N: Network> ToBytes for Transition<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.block_hash.write_le(&mut writer)?;
        self.local_commitments_root.write_le(&mut writer)?;
        self.serial_numbers.write_le(&mut writer)?;
        self.commitments.write_le(&mut writer)?;
        self.ciphertexts.write_le(&mut writer)?;
        self.value_balance.write_le(&mut writer)?;
        (self.events.len() as u16).write_le(&mut writer)?;
        self.events.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}
