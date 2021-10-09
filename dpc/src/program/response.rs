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

use crate::{Address, Network, PrivateKey, Record, RecordCiphertext};
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::{
    fmt::{
        Display,
        Formatter,
        {self},
    },
    io::{Read, Result as IoResult, Write},
};

// TODO (howardwu): TEMPORARY - Merge this into the Network trait.
use snarkvm_algorithms::traits::*;
pub type CiphertextRandomizer<N> = <<N as Network>::AccountEncryptionScheme as EncryptionScheme>::Randomness;

#[derive(Clone, Debug)]
pub struct Response<N: Network> {
    /// The records being produced.
    records: Vec<Record<N>>,
    /// The record ciphertexts.
    ciphertexts: Vec<RecordCiphertext<N>>,
    /// The record ciphertext randomizers.
    ciphertext_randomizers: Vec<CiphertextRandomizer<N>>,
}

impl<N: Network> Response<N> {
    /// Signs and returns a new instance of a response.
    pub fn new<R: Rng + CryptoRng>(records: Vec<Record<N>>, rng: &mut R) -> Result<Self> {
        // Compute the encrypted records.
        let (ciphertexts, ciphertext_randomizers) = Self::encrypt_records(&records, rng)?;

        Self::from(records, ciphertexts, ciphertext_randomizers)
    }

    /// Returns a new instance of a noop request.
    pub fn new_noop<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng);
        let noop_address = Address::from_private_key(&noop_private_key)?;

        let records = (0..N::NUM_OUTPUT_RECORDS)
            .map(|_| Ok(Record::new_noop_output(noop_address, Default::default(), rng)?))
            .collect::<Result<Vec<_>>>()?;

        // Compute the encrypted records.
        let (ciphertexts, ciphertext_randomizers) = Self::encrypt_records(&records, rng)?;

        Self::from(records, ciphertexts, ciphertext_randomizers)
    }

    pub fn from(
        records: Vec<Record<N>>,
        ciphertexts: Vec<RecordCiphertext<N>>,
        ciphertext_randomizers: Vec<CiphertextRandomizer<N>>,
    ) -> Result<Self> {
        Ok(Self {
            records,
            ciphertexts,
            ciphertext_randomizers,
        })
    }

    /// Returns `true` if the output records are the noop program.
    pub fn is_noop(&self) -> bool {
        self.records.iter().filter(|output| output.is_dummy()).count() == N::NUM_OUTPUT_RECORDS
    }

    /// Returns a reference to the records.
    pub fn records(&self) -> &Vec<Record<N>> {
        &self.records
    }

    /// Returns a reference to the ciphertexts.
    pub fn ciphertexts(&self) -> &Vec<RecordCiphertext<N>> {
        &self.ciphertexts
    }

    /// Returns a reference to the ciphertext randomizers.
    pub fn ciphertext_randomizers(&self) -> &Vec<CiphertextRandomizer<N>> {
        &self.ciphertext_randomizers
    }

    /// Returns the commitments.
    pub fn to_commitments(&self) -> Vec<N::Commitment> {
        self.records
            .iter()
            .take(N::NUM_OUTPUT_RECORDS)
            .map(|output| output.commitment())
            .collect()
    }

    #[inline]
    fn encrypt_records<R: Rng + CryptoRng>(
        output_records: &Vec<Record<N>>,
        rng: &mut R,
    ) -> Result<(Vec<RecordCiphertext<N>>, Vec<CiphertextRandomizer<N>>)> {
        let mut encrypted_records = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);
        let mut encrypted_record_randomizers = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);

        for record in output_records.iter().take(N::NUM_OUTPUT_RECORDS) {
            let (encrypted_record, encrypted_record_randomizer) = RecordCiphertext::encrypt(record, rng)?;
            encrypted_records.push(encrypted_record);
            encrypted_record_randomizers.push(encrypted_record_randomizer);
        }

        Ok((encrypted_records, encrypted_record_randomizers))
    }
}

impl<N: Network> FromBytes for Response<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut records = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            records.push(FromBytes::read_le(&mut reader)?);
        }

        let mut ciphertexts = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            ciphertexts.push(FromBytes::read_le(&mut reader)?);
        }

        let mut ciphertext_randomizers = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            ciphertext_randomizers.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self {
            records,
            ciphertexts,
            ciphertext_randomizers,
        })
    }
}

impl<N: Network> ToBytes for Response<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.records.write_le(&mut writer)?;
        self.ciphertexts.write_le(&mut writer)?;
        self.ciphertext_randomizers.write_le(&mut writer)
    }
}

impl<N: Network> Display for Response<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::testnet2::*;
//
//     use rand::{thread_rng, SeedableRng};
//     use rand_chacha::ChaChaRng;
//
//     const ITERATIONS: usize = 100;
//
//     #[test]
//     fn test_new_noop_and_to_record() {
//         for _ in 0..ITERATIONS {
//             // Sample a random seed for the RNG.
//             let seed: u64 = thread_rng().gen();
//
//             // Generate the given inputs.
//             let mut given_rng = ChaChaRng::seed_from_u64(seed);
//             let given_serial_numbers = {
//                 let mut serial_numbers = Vec::with_capacity(Testnet2::NUM_INPUT_RECORDS);
//                 for _ in 0..Testnet2::NUM_INPUT_RECORDS {
//                     let input = Input::<Testnet2>::new_noop(&mut given_rng).unwrap();
//                     serial_numbers.push(input.serial_number().clone());
//                 }
//                 serial_numbers
//             };
//
//             // Checkpoint the RNG and clone it.
//             let mut expected_rng = given_rng.clone();
//             let mut candidate_rng = given_rng.clone();
//
//             // Generate the expected output state.
//             let expected_record = {
//                 let account = Account::<Testnet2>::new(&mut expected_rng).unwrap();
//                 Record::new_noop_output(account.address, given_serial_numbers[0], &mut expected_rng).unwrap()
//             };
//
//             // Generate the candidate output state.
//             let (candidate_record, candidate_address, candidate_value, candidate_payload, candidate_program_id) = {
//                 let output = Output::new_noop(&mut candidate_rng).unwrap();
//                 let record = output.to_record(given_serial_numbers[0], &mut candidate_rng).unwrap();
//                 (
//                     record,
//                     output.address(),
//                     output.value(),
//                     output.payload().clone(),
//                     output.program_id(),
//                 )
//             };
//
//             assert_eq!(expected_record, candidate_record);
//             assert_eq!(expected_record.owner(), candidate_address);
//             assert_eq!(expected_record.value(), candidate_value.0 as u64);
//             assert_eq!(expected_record.payload(), &candidate_payload);
//             assert_eq!(expected_record.program_id(), candidate_program_id);
//         }
//     }
// }
