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

use crate::{prelude::*, Parameters, Transaction};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use std::io::{Read, Result as IoResult, Write};

/// The transaction kernel contains core (public) transaction components,
/// A signed transaction kernel implies the caller has authorized the execution
/// of the transaction, and implies these values are admissibleby the ledger.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    Debug(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct TransactionKernel<C: Parameters> {
    pub network_id: u8,
    pub serial_numbers: Vec<C::AccountSignaturePublicKey>,
    pub commitments: Vec<C::RecordCommitment>,
    pub value_balance: AleoAmount,
    pub memo: <Transaction<C> as TransactionScheme>::Memorandum,
}

impl<C: Parameters> TransactionKernel<C> {
    #[inline]
    pub fn to_signature_message(&self) -> Result<Vec<u8>> {
        self.to_bytes_le()
    }
}

impl<C: Parameters> ToBytes for TransactionKernel<C> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the correct number of serial numbers and commitments are provided.
        if self.serial_numbers.len() != C::NUM_INPUT_RECORDS || self.commitments.len() != C::NUM_OUTPUT_RECORDS {
            return Err(DPCError::Message(format!(
                "Transaction kernel size mismatch: serial numbers - {}, commitments - {}",
                self.serial_numbers.len(),
                self.commitments.len()
            ))
            .into());
        }

        self.network_id.write_le(&mut writer)?;
        self.serial_numbers.write_le(&mut writer)?;
        self.commitments.write_le(&mut writer)?;
        self.value_balance.write_le(&mut writer)?;
        self.memo.write_le(&mut writer)
    }
}

impl<C: Parameters> FromBytes for TransactionKernel<C> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let network_id: u8 = FromBytes::read_le(&mut reader)?;

        let mut serial_numbers = Vec::<C::AccountSignaturePublicKey>::with_capacity(C::NUM_INPUT_RECORDS);
        for _ in 0..C::NUM_INPUT_RECORDS {
            serial_numbers.push(FromBytes::read_le(&mut reader)?);
        }

        let mut commitments = Vec::<C::RecordCommitment>::with_capacity(C::NUM_OUTPUT_RECORDS);
        for _ in 0..C::NUM_OUTPUT_RECORDS {
            commitments.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance: AleoAmount = FromBytes::read_le(&mut reader)?;
        let memo: <Transaction<C> as TransactionScheme>::Memorandum = FromBytes::read_le(&mut reader)?;

        Ok(Self {
            network_id,
            serial_numbers,
            commitments,
            value_balance,
            memo,
        })
    }
}
