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
        events: Vec<Event<N>>,
    ) -> Result<Self> {
        Ok(Self { transition_id, records, encryption_randomness, value_balance, events })
    }

    /// Returns `true` if the output records are the noop program.
    pub fn is_noop(&self) -> bool {
        self.records.iter().filter(|output| output.is_dummy()).count() == N::NUM_OUTPUT_RECORDS
    }

    /// Returns the transition ID.
    pub fn transition_id(&self) -> N::TransitionID {
        self.transition_id
    }

    /// Returns the commitments.
    pub fn commitments(&self) -> Vec<N::Commitment> {
        self.records.iter().take(N::NUM_OUTPUT_RECORDS).map(Record::commitment).collect()
    }

    /// Returns a reference to the records.
    pub fn records(&self) -> &Vec<Record<N>> {
        &self.records
    }

    /// Returns the ciphertexts.
    pub fn ciphertexts(&self) -> Vec<N::RecordCiphertext> {
        self.records.iter().take(N::NUM_OUTPUT_RECORDS).map(Record::ciphertext).cloned().collect()
    }

    /// Returns a reference to the encryption randomness.
    pub fn encryption_randomness(&self) -> &Vec<EncryptionRandomness<N>> {
        &self.encryption_randomness
    }

    /// Returns the value balance.
    pub fn value_balance(&self) -> AleoAmount {
        self.value_balance
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

        let mut records = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            records.push(FromBytes::read_le(&mut reader)?);
        }

        let mut encryption_randomness = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            encryption_randomness.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance = FromBytes::read_le(&mut reader)?;

        let num_events: u16 = FromBytes::read_le(&mut reader)?;
        let mut events = Vec::with_capacity(num_events as usize);
        for _ in 0..num_events {
            events.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self { transition_id, records, encryption_randomness, value_balance, events })
    }
}

impl<N: Network> ToBytes for Response<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.transition_id.write_le(&mut writer)?;
        self.records.write_le(&mut writer)?;
        self.encryption_randomness.write_le(&mut writer)?;
        self.value_balance.write_le(&mut writer)?;
        (self.events.len() as u16).write_le(&mut writer)?;
        self.events.write_le(&mut writer)
    }
}

impl<N: Network> fmt::Display for Response<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
