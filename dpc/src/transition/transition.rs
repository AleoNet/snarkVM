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
use snarkvm_utilities::{has_duplicates, to_bytes_le, FromBytes, ToBytes};

use anyhow::Result;
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Transition<N: Network> {
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
}

impl<N: Network> Transition<N> {
    /// Initializes a new instance of a transition.
    #[inline]
    pub(crate) fn from(request: &Request<N>, response: &Response<N>) -> Result<Self> {
        // Fetch the block hash, local commitments root, and serial numbers.
        let block_hash = request.block_hash();
        let local_commitments_root = request.local_commitments_root();
        let serial_numbers = request.to_serial_numbers()?;

        // Fetch the commitments and ciphertexts.
        let commitments = response.to_commitments();
        let ciphertexts = response.ciphertexts().clone();

        // Compute the value balance.
        let mut value_balance = AleoAmount::ZERO;
        for record in request.records().iter().take(N::NUM_INPUT_RECORDS) {
            value_balance = value_balance.add(AleoAmount::from_bytes(record.value() as i64));
        }
        for record in response.records().iter().take(N::NUM_OUTPUT_RECORDS) {
            value_balance = value_balance.sub(AleoAmount::from_bytes(record.value() as i64));
        }

        // Construct the transition.
        let transition = Self {
            block_hash,
            local_commitments_root,
            serial_numbers,
            commitments,
            ciphertexts,
            value_balance,
        };

        // Ensure the transition is well-formed.
        match transition.is_valid() {
            true => Ok(transition),
            false => Err(TransactionError::InvalidTransition(
                transition.serial_numbers.len(),
                transition.commitments.len(),
                transition.ciphertexts.len(),
            )
            .into()),
        }
    }

    /// Returns `true` if the transition is well-formed.
    #[inline]
    pub(crate) fn is_valid(&self) -> bool {
        // Returns `false` if the number of serial numbers in the transition is incorrect.
        if self.serial_numbers().len() != N::NUM_INPUT_RECORDS {
            eprintln!("Transition contains incorrect number of serial numbers");
            return false;
        }

        // Returns `false` if there are duplicate serial numbers in the transition.
        if has_duplicates(self.serial_numbers().iter()) {
            eprintln!("Transition contains duplicate serial numbers");
            return false;
        }

        // Returns `false` if the number of commitments in the transition is incorrect.
        if self.commitments().len() != N::NUM_OUTPUT_RECORDS {
            eprintln!("Transition contains incorrect number of commitments");
            return false;
        }

        // Returns `false` if there are duplicate commitments numbers in the transition.
        if has_duplicates(self.commitments().iter()) {
            eprintln!("Transition contains duplicate commitments");
            return false;
        }

        // Returns `false` if the number of record ciphertexts in the transition is incorrect.
        if self.ciphertexts().len() != N::NUM_OUTPUT_RECORDS {
            eprintln!("Transition contains incorrect number of record ciphertexts");
            return false;
        }

        // Returns `false` if there are duplicate ciphertexts in the transition.
        if has_duplicates(self.ciphertexts().iter()) {
            eprintln!("Transition contains duplicate ciphertexts");
            return false;
        }

        true
    }

    /// Returns the block hash used to prove inclusion of ledger-consumed records.
    #[inline]
    pub(crate) fn block_hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the local commitments root used to prove inclusion of locally-consumed records.
    #[inline]
    pub(crate) fn local_commitments_root(&self) -> N::LocalCommitmentsRoot {
        self.local_commitments_root
    }

    /// Returns a reference to the serial numbers.
    #[inline]
    pub(crate) fn serial_numbers(&self) -> &Vec<N::SerialNumber> {
        &self.serial_numbers
    }

    /// Returns a reference to the commitments.
    #[inline]
    pub(crate) fn commitments(&self) -> &Vec<N::Commitment> {
        &self.commitments
    }

    /// Returns a reference to the ciphertexts.
    #[inline]
    pub(crate) fn ciphertexts(&self) -> &Vec<RecordCiphertext<N>> {
        &self.ciphertexts
    }

    /// Returns a reference to the value balance.
    #[inline]
    pub(crate) fn value_balance(&self) -> &AleoAmount {
        &self.value_balance
    }

    /// Returns the ciphertext IDs.
    #[inline]
    pub(crate) fn to_ciphertext_ids(&self) -> Result<Vec<N::CiphertextID>> {
        self.ciphertexts.iter().map(|c| Ok(c.to_ciphertext_id()?)).collect()
    }

    /// Transition ID := Hash(block hash || local commitments root || serial numbers || commitments || ciphertext_ids || value balance)
    #[inline]
    pub(crate) fn to_transition_id(&self) -> Result<N::TransitionID> {
        Ok(N::transition_id_crh().hash(&to_bytes_le![
            self.block_hash,
            self.local_commitments_root,
            self.serial_numbers,
            self.commitments,
            self.to_ciphertext_ids()?,
            self.value_balance
        ]?)?)
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
        self.value_balance.write_le(&mut writer)
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

        let transition = Self {
            block_hash,
            local_commitments_root,
            serial_numbers,
            commitments,
            ciphertexts,
            value_balance,
        };

        // Ensure the transition is well-formed.
        match transition.is_valid() {
            true => Ok(transition),
            false => Err(TransactionError::InvalidTransition(
                transition.serial_numbers.len(),
                transition.commitments.len(),
                transition.ciphertexts.len(),
            )
            .into()),
        }
    }
}

// TODO (raychu): add debug support for record ciphertexts
impl<N: Network> fmt::Debug for Transition<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Transition {{ block_hash: {:?}, local_commitments_root: {:?}, serial_numbers: {:?}, commitments: {:?}, ciphertext_ids: {:?}, value_balance: {:?} }}",
            self.block_hash(),
            self.local_commitments_root(),
            self.serial_numbers(),
            self.commitments(),
            self.to_ciphertext_ids().unwrap(),
            self.value_balance(),
        )
    }
}
