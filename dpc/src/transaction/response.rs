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

use crate::{AleoAmount, Event, Network, Record};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
};

// TODO (howardwu): TEMPORARY - Merge this into the Network trait.
use snarkvm_algorithms::traits::*;
pub type EncryptionRandomness<N> = <<N as Network>::AccountEncryptionScheme as EncryptionScheme>::ScalarRandomness;

#[derive(Clone, Debug)]
pub struct Response<N: Network> {
    /// The ID of the transition.
    transition_id: N::TransitionID,
    /// The records being produced.
    records: Vec<Record<N>>,
    /// The record encryption randomness.
    encryption_randomness: Vec<EncryptionRandomness<N>>,
    /// A value balance is the difference between the input and output record values.
    value_balance: AleoAmount,
    /// The commitments on the input record values.
    input_value_commitments: Vec<N::ValueCommitment>,
    /// The commitments on the output record values.
    output_value_commitments: Vec<N::ValueCommitment>,
    /// The randomness used to generate the input value commitments.
    input_value_commitment_randomness: Vec<N::ProgramScalarField>,
    /// The randomness used to generate the output value commitments.
    output_value_commitment_randomness: Vec<N::ProgramScalarField>,
    /// The value balance commitment.
    value_balance_commitment: N::ValueBalanceCommitment,
    /// The events emitted from the execution.
    events: Vec<Event<N>>,
}

impl<N: Network> Response<N> {
    /// Returns a new instance of a response.
    pub fn new(
        transition_id: N::TransitionID,
        records: Vec<Record<N>>,
        encryption_randomness: Vec<EncryptionRandomness<N>>,
        value_balance: AleoAmount,
        input_value_commitments: Vec<N::ValueCommitment>,
        output_value_commitments: Vec<N::ValueCommitment>,
        input_value_commitment_randomness: Vec<N::ProgramScalarField>,
        output_value_commitment_randomness: Vec<N::ProgramScalarField>,
        value_balance_commitment: N::ValueBalanceCommitment,
        events: Vec<Event<N>>,
    ) -> Result<Self> {
        Ok(Self {
            transition_id,
            records,
            encryption_randomness,
            value_balance,
            input_value_commitments,
            output_value_commitments,
            input_value_commitment_randomness,
            output_value_commitment_randomness,
            value_balance_commitment,
            events,
        })
    }

    /// Returns `true` if the output records are the noop program.
    pub fn is_noop(&self) -> bool {
        self.records.iter().all(|output| output.is_dummy())
    }

    /// Returns the transition ID.
    pub fn transition_id(&self) -> N::TransitionID {
        self.transition_id
    }

    /// Returns the commitments.
    pub fn commitments(&self) -> Vec<N::Commitment> {
        self.records.iter().take(N::NUM_OUTPUTS as usize).map(Record::commitment).collect()
    }

    /// Returns a reference to the records.
    pub fn records(&self) -> &Vec<Record<N>> {
        &self.records
    }

    /// Returns the ciphertexts.
    pub fn ciphertexts(&self) -> Vec<N::RecordCiphertext> {
        self.records.iter().take(N::NUM_OUTPUTS as usize).map(Record::ciphertext).cloned().collect()
    }

    /// Returns a reference to the encryption randomness.
    pub fn encryption_randomness(&self) -> &Vec<EncryptionRandomness<N>> {
        &self.encryption_randomness
    }

    /// Returns the value balance.
    pub fn value_balance(&self) -> AleoAmount {
        self.value_balance
    }

    /// Returns the commitments on the input record values.
    pub fn input_value_commitments(&self) -> &Vec<N::ValueCommitment> {
        &self.input_value_commitments
    }

    /// Returns the commitments on the output record values.
    pub fn output_value_commitments(&self) -> &Vec<N::ValueCommitment> {
        &self.output_value_commitments
    }

    /// Returns the randomness used to generate the input value commitments.
    pub fn input_value_commitment_randomness(&self) -> &Vec<N::ProgramScalarField> {
        &self.input_value_commitment_randomness
    }

    /// Returns the randomness used to generate the output value commitments.
    pub fn output_value_commitment_randomness(&self) -> &Vec<N::ProgramScalarField> {
        &self.output_value_commitment_randomness
    }

    /// Returns the value balance commitment.
    pub fn value_balance_commitment(&self) -> &N::ValueBalanceCommitment {
        &self.value_balance_commitment
    }

    /// Returns a reference to the events.
    pub fn events(&self) -> &Vec<Event<N>> {
        &self.events
    }
}

impl<N: Network> FromBytes for Response<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let transition_id = FromBytes::read_le(&mut reader)?;

        let num_output_records: u32 = FromBytes::read_le(&mut reader)?;

        let mut records = Vec::with_capacity(num_output_records as usize);
        for _ in 0..num_output_records {
            records.push(FromBytes::read_le(&mut reader)?);
        }

        let mut encryption_randomness = Vec::with_capacity(num_output_records as usize);
        for _ in 0..num_output_records {
            encryption_randomness.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance = FromBytes::read_le(&mut reader)?;

        let num_input_records: u32 = FromBytes::read_le(&mut reader)?;

        let mut input_value_commitments = Vec::with_capacity(num_input_records as usize);
        for _ in 0..num_input_records {
            input_value_commitments.push(FromBytes::read_le(&mut reader)?);
        }

        let mut output_value_commitments = Vec::with_capacity(num_output_records as usize);
        for _ in 0..num_output_records {
            output_value_commitments.push(FromBytes::read_le(&mut reader)?);
        }

        let mut input_value_commitment_randomness = Vec::with_capacity(num_input_records as usize);
        for _ in 0..num_input_records {
            input_value_commitment_randomness.push(FromBytes::read_le(&mut reader)?);
        }

        let mut output_value_commitment_randomness = Vec::with_capacity(num_output_records as usize);
        for _ in 0..num_output_records {
            output_value_commitment_randomness.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance_commitment = FromBytes::read_le(&mut reader)?;

        let num_events: u16 = FromBytes::read_le(&mut reader)?;
        let mut events = Vec::with_capacity(num_events as usize);
        for _ in 0..num_events {
            events.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self {
            transition_id,
            records,
            encryption_randomness,
            value_balance,
            input_value_commitments,
            output_value_commitments,
            input_value_commitment_randomness,
            output_value_commitment_randomness,
            value_balance_commitment,
            events,
        })
    }
}

impl<N: Network> ToBytes for Response<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.transition_id.write_le(&mut writer)?;
        (self.records.len() as u32).write_le(&mut writer)?;
        self.records.write_le(&mut writer)?;
        self.encryption_randomness.write_le(&mut writer)?;
        self.value_balance.write_le(&mut writer)?;
        (self.input_value_commitments.len() as u32).write_le(&mut writer)?;
        self.input_value_commitments.write_le(&mut writer)?;
        self.output_value_commitments.write_le(&mut writer)?;
        self.input_value_commitment_randomness.write_le(&mut writer)?;
        self.output_value_commitment_randomness.write_le(&mut writer)?;
        self.value_balance_commitment.write_le(&mut writer)?;
        (self.events.len() as u16).write_le(&mut writer)?;
        self.events.write_le(&mut writer)
    }
}

impl<N: Network> fmt::Display for Response<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
