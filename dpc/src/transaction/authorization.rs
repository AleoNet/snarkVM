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
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes, UniformRand};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::{
    collections::HashSet,
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

type EncryptedRecordID<N> = <<N as Network>::EncryptedRecordCRH as CRH>::Output;
type EncryptedRecordRandomizer<N> = <<N as Network>::AccountEncryptionScheme as EncryptionScheme>::Randomness;
type ProgramCommitment<N> = <<N as Network>::ProgramCommitmentScheme as CommitmentScheme>::Output;
type ProgramCommitmentRandomness<N> = <<N as Network>::ProgramCommitmentScheme as CommitmentScheme>::Randomness;

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
    pub fn to_local_data<R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<LocalData<N>> {
        Ok(LocalData::new(
            &self.kernel,
            &self.input_records,
            &self.output_records,
            rng,
        )?)
    }

    #[inline]
    pub fn to_program_commitment<R: Rng + CryptoRng>(
        &self,
        rng: &mut R,
    ) -> Result<(ProgramCommitment<N>, ProgramCommitmentRandomness<N>)> {
        let program_id = self
            .input_records
            .iter()
            .chain(self.output_records.iter())
            .take(N::NUM_TOTAL_RECORDS)
            .map(|record| record.program_id())
            .filter(|program_id| program_id != N::noop_program_id())
            .collect::<HashSet<_>>();

        // Ensure the number of unique programs is within the declared limit.
        if program_id.len() > 1 {
            return Err(anyhow!("Expected 1 program ID, found {} program IDs", program_id.len()));
        }

        //
        // TODO (howardwu): This still does not correctly construct the program commitment.
        //  There are 2 cases unaccounted for: 1) need to pad with noop program IDs, 2) when two executables are of the same program ID.

        // Flatten and concatenate the program IDs into bytes.
        let program_ids_bytes = program_id
            .iter()
            .flat_map(|program_id| program_id.to_bytes_le().expect("Failed to convert program ID to bytes"))
            .collect::<Vec<u8>>();

        let program_randomness = UniformRand::rand(rng);
        let program_commitment = N::program_commitment_scheme().commit(&program_ids_bytes, &program_randomness)?;
        Ok((program_commitment, program_randomness))
    }

    #[inline]
    pub fn to_encrypted_records<R: Rng + CryptoRng>(
        &self,
        rng: &mut R,
    ) -> Result<(
        Vec<EncryptedRecord<N>>,
        Vec<EncryptedRecordID<N>>,
        Vec<EncryptedRecordRandomizer<N>>,
    )> {
        let mut encrypted_records = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);
        let mut encrypted_record_ids = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);
        let mut encrypted_record_randomizers = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);

        for record in self.output_records.iter().take(N::NUM_OUTPUT_RECORDS) {
            let (encrypted_record, encrypted_record_randomizer) = EncryptedRecord::encrypt(record, rng)?;
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
