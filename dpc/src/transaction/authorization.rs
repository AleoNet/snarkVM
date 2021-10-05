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

use crate::prelude::*;
use snarkvm_algorithms::prelude::*;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

type EncryptedRecordID<N> = <<N as Network>::EncryptedRecordCRH as CRH>::Output;
type EncryptedRecordRandomizer<N> = <<N as Network>::AccountEncryptionScheme as EncryptionScheme>::Randomness;

/// The transaction authorization contains caller signatures and is required to
/// produce the final transaction proof.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct TransactionAuthorization<N: Network> {
    pub kernel: TransactionKernel<N>,
    pub input_records: Vec<Record<N>>,
    pub output_records: Vec<Record<N>>,
    pub signatures: Vec<N::AccountSignature>,
}

impl<N: Network> TransactionAuthorization<N> {
    #[inline]
    pub fn from(transition: &StateTransition<N>, signatures: Vec<N::AccountSignature>) -> Self {
        debug_assert!(transition.kernel().is_valid());
        debug_assert_eq!(N::NUM_INPUT_RECORDS, transition.input_records().len());
        debug_assert_eq!(N::NUM_OUTPUT_RECORDS, transition.output_records().len());
        debug_assert_eq!(N::NUM_INPUT_RECORDS, signatures.len());

        Self {
            kernel: transition.kernel().clone(),
            input_records: transition.input_records().clone(),
            output_records: transition.output_records().clone(),
            signatures,
        }
    }

    #[inline]
    pub fn to_transaction_id(&self) -> Result<N::TransactionID> {
        self.kernel.to_transaction_id()
    }

    #[inline]
    pub fn to_encrypted_records<R: Rng + CryptoRng>(
        &self,
        rng: &mut R,
    ) -> Result<(
        Vec<RecordCiphertext<N>>,
        Vec<EncryptedRecordID<N>>,
        Vec<EncryptedRecordRandomizer<N>>,
    )> {
        let mut encrypted_records = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);
        let mut encrypted_record_ids = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);
        let mut encrypted_record_randomizers = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);

        for record in self.output_records.iter().take(N::NUM_OUTPUT_RECORDS) {
            let (encrypted_record, encrypted_record_randomizer) = RecordCiphertext::encrypt(record, rng)?;
            encrypted_record_ids.push(encrypted_record.to_hash()?);
            encrypted_records.push(encrypted_record);
            encrypted_record_randomizers.push(encrypted_record_randomizer);
        }

        Ok((encrypted_records, encrypted_record_ids, encrypted_record_randomizers))
    }
}

impl<N: Network> ToBytes for TransactionAuthorization<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.kernel.write_le(&mut writer)?;
        self.input_records.write_le(&mut writer)?;
        self.output_records.write_le(&mut writer)?;
        self.signatures.write_le(&mut writer)?;
        Ok(())
    }
}

impl<N: Network> FromBytes for TransactionAuthorization<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let kernel: TransactionKernel<N> = FromBytes::read_le(&mut reader)?;

        let mut input_records = Vec::<Record<N>>::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            input_records.push(FromBytes::read_le(&mut reader)?);
        }

        let mut output_records = Vec::<Record<N>>::with_capacity(N::NUM_OUTPUT_RECORDS);
        for _ in 0..N::NUM_OUTPUT_RECORDS {
            output_records.push(FromBytes::read_le(&mut reader)?);
        }

        let mut signatures = Vec::<N::AccountSignature>::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            signatures.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self {
            kernel,
            input_records,
            output_records,
            signatures,
        })
    }
}

impl<N: Network> FromStr for TransactionAuthorization<N> {
    type Err = DPCError;

    fn from_str(kernel: &str) -> Result<Self, Self::Err> {
        Ok(Self::read_le(&hex::decode(kernel)?[..])?)
    }
}

impl<N: Network> fmt::Display for TransactionAuthorization<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            hex::encode(to_bytes_le![self].expect("couldn't serialize to bytes"))
        )
    }
}
