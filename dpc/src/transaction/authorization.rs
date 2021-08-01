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

use crate::{prelude::*, EncryptedRecord, Parameters, Record};
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

/// The transaction authorization contains caller signatures and is required to
/// produce the final transaction proof.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    Debug(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct TransactionAuthorization<C: Parameters> {
    pub kernel: TransactionKernel<C>,
    pub old_records: Vec<Record<C>>,
    pub new_records: Vec<Record<C>>,
    pub signatures: Vec<<C::AccountSignatureScheme as SignatureScheme>::Signature>,
}

impl<C: Parameters> TransactionAuthorization<C> {
    #[inline]
    pub fn to_local_data<R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<LocalData<C>> {
        Ok(LocalData::new(&self.kernel, &self.old_records, &self.new_records, rng)?)
    }

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

impl<C: Parameters> ToBytes for TransactionAuthorization<C> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.kernel.write_le(&mut writer)?;
        self.old_records.write_le(&mut writer)?;
        self.new_records.write_le(&mut writer)?;
        self.signatures.write_le(&mut writer)
    }
}

impl<C: Parameters> FromBytes for TransactionAuthorization<C> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let kernel: TransactionKernel<C> = FromBytes::read_le(&mut reader)?;

        let mut old_records = Vec::<Record<C>>::with_capacity(C::NUM_INPUT_RECORDS);
        for _ in 0..C::NUM_INPUT_RECORDS {
            old_records.push(FromBytes::read_le(&mut reader)?);
        }

        let mut new_records = Vec::<Record<C>>::with_capacity(C::NUM_OUTPUT_RECORDS);
        for _ in 0..C::NUM_OUTPUT_RECORDS {
            new_records.push(FromBytes::read_le(&mut reader)?);
        }

        let mut signatures =
            Vec::<<C::AccountSignatureScheme as SignatureScheme>::Signature>::with_capacity(C::NUM_INPUT_RECORDS);
        for _ in 0..C::NUM_INPUT_RECORDS {
            signatures.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self {
            kernel,
            old_records,
            new_records,
            signatures,
        })
    }
}

impl<C: Parameters> FromStr for TransactionAuthorization<C> {
    type Err = DPCError;

    fn from_str(kernel: &str) -> Result<Self, Self::Err> {
        Ok(Self::read_le(&hex::decode(kernel)?[..])?)
    }
}

impl<C: Parameters> fmt::Display for TransactionAuthorization<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            hex::encode(to_bytes_le![self].expect("couldn't serialize to bytes"))
        )
    }
}
