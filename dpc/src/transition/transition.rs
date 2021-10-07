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

use crate::{prelude::*, Network};
use snarkvm_algorithms::traits::CRH;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::Result;
use std::io::{Read, Result as IoResult, Write};

/// The transition contains core (public) transaction components,
/// A signed transition implies the caller has authorized the execution
/// of the transition, and implies these values are admissible by the ledger.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Transition<N: Network> {
    /// The serial numbers of the input records.
    serial_numbers: Vec<N::SerialNumber>,
    /// The commitments of the output records.
    commitments: Vec<N::Commitment>,
    /// The ciphertexts of the output records.
    ciphertexts: Vec<RecordCiphertext<N>>,
    /// A value balance is the difference between the input and output record values.
    value_balance: AleoAmount,
}

impl<N: Network> Transition<N> {
    /// Initializes a new instance of a transition.
    #[inline]
    pub fn new(
        serial_numbers: Vec<N::SerialNumber>,
        commitments: Vec<N::Commitment>,
        ciphertexts: Vec<RecordCiphertext<N>>,
        value_balance: AleoAmount,
    ) -> Result<Self> {
        // Construct the transition.
        let kernel = Self {
            serial_numbers,
            commitments,
            ciphertexts,
            value_balance,
        };

        // Ensure the transition is well-formed.
        match kernel.is_valid() {
            true => Ok(kernel),
            false => Err(DPCError::InvalidTransition(
                kernel.serial_numbers.len(),
                kernel.commitments.len(),
                kernel.ciphertexts.len(),
            )
            .into()),
        }
    }

    /// Returns `true` if the transition is well-formed.
    #[inline]
    pub fn is_valid(&self) -> bool {
        self.serial_numbers.len() == N::NUM_INPUT_RECORDS
            && self.commitments.len() == N::NUM_OUTPUT_RECORDS
            && self.ciphertexts.len() == N::NUM_OUTPUT_RECORDS
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

    /// Returns the ciphertext IDs.
    #[inline]
    pub fn to_ciphertext_ids(&self) -> Result<Vec<N::CiphertextID>> {
        self.ciphertexts().iter().map(|c| Ok(c.to_hash()?)).collect()
    }

    /// Transaction ID = Hash(serial numbers || commitments || ciphertext_ids || value balance)
    #[inline]
    pub fn to_transaction_id(&self) -> Result<N::TransactionID> {
        let preimage = to_bytes_le![
            self.serial_numbers,
            self.commitments,
            self.to_ciphertext_ids()?,
            self.value_balance
        ]?;

        Ok(N::transaction_id_crh().hash(&preimage)?)
    }
}

impl<N: Network> ToBytes for Transition<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the correct number of serial numbers and commitments are provided.
        if !self.is_valid() {
            return Err(DPCError::InvalidTransition(
                self.serial_numbers.len(),
                self.commitments.len(),
                self.ciphertexts.len(),
            )
            .into());
        }

        self.serial_numbers.write_le(&mut writer)?;
        self.commitments.write_le(&mut writer)?;
        self.ciphertexts.write_le(&mut writer)?;
        self.value_balance.write_le(&mut writer)
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

        let mut ciphertexts = Vec::<RecordCiphertext<N>>::with_capacity(N::NUM_OUTPUT_RECORDS);
        for _ in 0..N::NUM_OUTPUT_RECORDS {
            ciphertexts.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance: AleoAmount = FromBytes::read_le(&mut reader)?;

        Ok(Self::new(serial_numbers, commitments, ciphertexts, value_balance)
            .expect("Failed to initialize a transition"))
    }
}
