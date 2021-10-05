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

use crate::{Address, DPCError, Network, Payload, Record, ViewKey};
use snarkvm_algorithms::traits::{CommitmentScheme, EncryptionScheme, CRH};
use snarkvm_utilities::{
    io::{Cursor, Result as IoResult},
    marker::PhantomData,
    to_bytes_le,
    FromBytes,
    Read,
    ToBytes,
    Write,
};

use anyhow::{anyhow, Result};
use rand::{thread_rng, CryptoRng, Rng};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct EncryptedRecord<N: Network> {
    ciphertext: Vec<u8>,
    phantom: PhantomData<N>,
}

impl<N: Network> EncryptedRecord<N> {
    pub fn new(ciphertext: Vec<u8>) -> Self {
        Self {
            ciphertext,
            phantom: PhantomData,
        }
    }

    /// Encrypt the given vector of records and returns
    /// 1. Encrypted record
    /// 2. Encryption randomness
    pub fn encrypt<R: Rng + CryptoRng>(
        record: &Record<N>,
        rng: &mut R,
    ) -> Result<(
        Self,
        <<N as Network>::AccountEncryptionScheme as EncryptionScheme>::Randomness,
    )> {
        // Convert the record into bytes.
        let buffer = to_bytes_le![
            record.value(),
            record.payload(),
            record.program_id(),
            record.serial_number_nonce(),
            record.commitment_randomness()
        ]?;

        // Ensure the record bytes are within the permitted size.
        if buffer.len() > u16::MAX as usize {
            return Err(anyhow!("Records must be <= 65535 bytes, found {} bytes", buffer.len()));
        }

        // Encrypt the record bytes.
        let randomizer = N::account_encryption_scheme().generate_randomness(rng)?;
        let ciphertext = N::account_encryption_scheme().encrypt(&*record.owner(), &randomizer, &buffer)?;

        Ok((Self::new(ciphertext), randomizer))
    }

    /// Decrypt and reconstruct the encrypted record.
    pub fn decrypt(&self, account_view_key: &ViewKey<N>) -> Result<Record<N>, DPCError> {
        // Decrypt the encrypted record
        let plaintext = N::account_encryption_scheme().decrypt(&*account_view_key, &self.ciphertext)?;

        let mut cursor = Cursor::new(plaintext);

        // Value
        let value = u64::read_le(&mut cursor)?;

        // Payload
        let payload = Payload::read_le(&mut cursor)?;

        // Program ID
        let program_id: N::ProgramID = FromBytes::read_le(&mut cursor)?;

        // Serial number nonce
        let serial_number_nonce = N::SerialNumber::read_le(&mut cursor)?;

        // Commitment randomness
        let commitment_randomness = <N::CommitmentScheme as CommitmentScheme>::Randomness::read_le(&mut cursor)?;

        // Construct the record account address
        let owner = Address::from_view_key(&account_view_key)?;

        Ok(Record::from(
            owner,
            value,
            payload,
            program_id,
            serial_number_nonce,
            commitment_randomness,
        )?)
    }

    /// Returns the encrypted record ID.
    /// The hash input is the ciphertext x-coordinates appended with the selector bits.
    pub fn to_hash(&self) -> Result<N::EncryptedRecordID, DPCError> {
        Ok(N::encrypted_record_crh().hash(&self.ciphertext)?)
    }
}

impl<N: Network> Default for EncryptedRecord<N> {
    fn default() -> Self {
        let (record, _randomness) = Self::encrypt(&Record::default(), &mut thread_rng()).unwrap();
        record
    }
}

impl<N: Network> ToBytes for EncryptedRecord<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.ciphertext.len() as u16).write_le(&mut writer)?;
        self.ciphertext.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for EncryptedRecord<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let ciphertext_len = u16::read_le(&mut reader)?;
        let mut ciphertext = Vec::with_capacity(ciphertext_len as usize);
        for _ in 0..ciphertext_len {
            ciphertext.push(u8::read_le(&mut reader)?);
        }

        Ok(Self::new(ciphertext))
    }
}
