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

use crate::{prelude::*, EncryptedRecord, Parameters, Record, Transaction};
use snarkvm_algorithms::prelude::*;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes, UniformRand};

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

type EncryptedRecordHash<C> = <<C as Parameters>::EncryptedRecordCRH as CRH>::Output;
type EncryptedRecordRandomizer<C> = <<C as Parameters>::AccountEncryptionScheme as EncryptionScheme>::Randomness;
type ProgramCommitment<C> = <<C as Parameters>::ProgramCommitmentScheme as CommitmentScheme>::Output;
type ProgramCommitmentRandomness<C> = <<C as Parameters>::ProgramCommitmentScheme as CommitmentScheme>::Randomness;

/// The transaction authorization are signatures over core (public) transaction components,
/// and authorized by the caller of the transaction. A signed transaction core implies
/// a transaction generated based on these values will be admissible by the ledger.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    Debug(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct TransactionAuthorization<C: Parameters> {
    pub network_id: u8,
    pub serial_numbers: Vec<C::AccountSignaturePublicKey>,
    pub commitments: Vec<C::RecordCommitment>,
    pub value_balance: AleoAmount,
    pub memo: <Transaction<C> as TransactionScheme>::Memorandum,
    pub signatures: Vec<<C::AccountSignatureScheme as SignatureScheme>::Signature>,
}

impl<C: Parameters> ToBytes for TransactionAuthorization<C> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.network_id.write_le(&mut writer)?;
        self.serial_numbers.write_le(&mut writer)?;
        self.commitments.write_le(&mut writer)?;
        self.value_balance.write_le(&mut writer)?;
        self.memo.write_le(&mut writer)?;
        self.signatures.write_le(&mut writer)
    }
}

impl<C: Parameters> FromBytes for TransactionAuthorization<C> {
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

        let mut signatures =
            Vec::<<C::AccountSignatureScheme as SignatureScheme>::Signature>::with_capacity(C::NUM_INPUT_RECORDS);
        for _ in 0..C::NUM_INPUT_RECORDS {
            signatures.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self {
            network_id,
            serial_numbers,
            commitments,
            value_balance,
            memo,
            signatures,
        })
    }
}

/// The transaction kernel contains components required to produce the final transaction proof
/// after `execute_offline_phase` has created serial numbers, commitments, and signatures.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    Debug(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct TransactionKernel<C: Parameters> {
    pub authorized: TransactionAuthorization<C>,
    pub old_records: Vec<Record<C>>,
    pub new_records: Vec<Record<C>>,
    pub local_data: LocalData<C>,
}

impl<C: Parameters> TransactionKernel<C> {
    #[inline]
    pub fn to_program_commitment<R: Rng + CryptoRng>(
        &self,
        rng: &mut R,
    ) -> Result<(ProgramCommitment<C>, ProgramCommitmentRandomness<C>)> {
        let program_ids = self
            .old_records
            .iter()
            .chain(self.new_records.iter())
            .take(C::NUM_TOTAL_RECORDS)
            .flat_map(|r| r.program_id())
            .cloned()
            .collect::<Vec<u8>>();

        let program_randomness = UniformRand::rand(rng);
        let program_commitment = C::program_commitment_scheme().commit(&program_ids, &program_randomness)?;
        Ok((program_commitment, program_randomness))
    }

    #[inline]
    pub fn to_encrypted_records<R: Rng + CryptoRng>(
        &self,
        rng: &mut R,
    ) -> Result<(
        Vec<EncryptedRecord<C>>,
        Vec<EncryptedRecordHash<C>>,
        Vec<EncryptedRecordRandomizer<C>>,
    )> {
        let mut encrypted_records = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        let mut encrypted_record_hashes = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        let mut encrypted_record_randomizers = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);

        for record in self.new_records.iter().take(C::NUM_OUTPUT_RECORDS) {
            let (encrypted_record, encrypted_record_randomizer) = EncryptedRecord::encrypt(record, rng)?;
            encrypted_record_hashes.push(encrypted_record.to_hash()?);
            encrypted_records.push(encrypted_record);
            encrypted_record_randomizers.push(encrypted_record_randomizer);
        }

        Ok((encrypted_records, encrypted_record_hashes, encrypted_record_randomizers))
    }
}

impl<C: Parameters> ToBytes for TransactionKernel<C> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.authorized.write_le(&mut writer)?;
        self.old_records.write_le(&mut writer)?;
        self.new_records.write_le(&mut writer)?;
        self.local_data.write_le(&mut writer)
    }
}

impl<C: Parameters> FromBytes for TransactionKernel<C> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let authorized: TransactionAuthorization<C> = FromBytes::read_le(&mut reader)?;

        let mut old_records = Vec::<Record<C>>::with_capacity(C::NUM_INPUT_RECORDS);
        for _ in 0..C::NUM_INPUT_RECORDS {
            old_records.push(FromBytes::read_le(&mut reader)?);
        }

        let mut new_records = Vec::<Record<C>>::with_capacity(C::NUM_OUTPUT_RECORDS);
        for _ in 0..C::NUM_OUTPUT_RECORDS {
            new_records.push(FromBytes::read_le(&mut reader)?);
        }

        let local_data: LocalData<C> = FromBytes::read_le(&mut reader)?;

        Ok(Self {
            authorized,
            old_records,
            new_records,
            local_data,
        })
    }
}

impl<C: Parameters> FromStr for TransactionKernel<C> {
    type Err = DPCError;

    fn from_str(kernel: &str) -> Result<Self, Self::Err> {
        Ok(Self::read_le(&hex::decode(kernel)?[..])?)
    }
}

impl<C: Parameters> fmt::Display for TransactionKernel<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            hex::encode(to_bytes_le![self].expect("couldn't serialize to bytes"))
        )
    }
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters"),
    Debug(bound = "C: Parameters")
)]
pub struct ExecutionKernel<C: Parameters> {
    pub new_records_encryption_randomness: Vec<<C::AccountEncryptionScheme as EncryptionScheme>::Randomness>,
    pub new_encrypted_records: Vec<EncryptedRecord<C>>,
}

impl<C: Parameters> ToBytes for ExecutionKernel<C> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.new_records_encryption_randomness.write_le(&mut writer)?;
        self.new_encrypted_records.write_le(&mut writer)
    }
}

impl<C: Parameters> FromBytes for ExecutionKernel<C> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut new_records_encryption_randomness = vec![];
        for _ in 0..C::NUM_OUTPUT_RECORDS {
            let encryption_randomness: <C::AccountEncryptionScheme as EncryptionScheme>::Randomness =
                FromBytes::read_le(&mut reader)?;
            new_records_encryption_randomness.push(encryption_randomness);
        }

        let mut new_encrypted_records = vec![];
        for _ in 0..C::NUM_OUTPUT_RECORDS {
            let encrypted_record: EncryptedRecord<C> = FromBytes::read_le(&mut reader)?;
            new_encrypted_records.push(encrypted_record);
        }

        Ok(Self {
            new_records_encryption_randomness,
            new_encrypted_records,
        })
    }
}

impl<C: Parameters> FromStr for ExecutionKernel<C> {
    type Err = DPCError;

    fn from_str(kernel: &str) -> Result<Self, Self::Err> {
        Ok(Self::read_le(&hex::decode(kernel)?[..])?)
    }
}

impl<C: Parameters> fmt::Display for ExecutionKernel<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            hex::encode(to_bytes_le![self].expect("couldn't serialize to bytes"))
        )
    }
}
