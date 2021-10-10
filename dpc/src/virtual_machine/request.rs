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

use crate::{
    Address,
    AleoAmount,
    ComputeKey,
    FunctionType,
    LedgerProof,
    LocalProof,
    Network,
    Operation,
    PrivateKey,
    Record,
};
use snarkvm_algorithms::SignatureScheme;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use once_cell::sync::OnceCell;
use rand::{CryptoRng, Rng};
use std::{
    collections::HashSet,
    fmt,
    io::{Read, Result as IoResult, Write},
};

#[derive(Clone, Debug)]
pub struct Request<N: Network> {
    /// The records being consumed.
    records: Vec<Record<N>>,
    /// The operation being performed.
    operation: Operation<N>,
    /// The inclusion proof of ledger-consumed records.
    ledger_proof: LedgerProof<N>,
    /// The inclusion proof of locally-consumed records.
    local_proof: LocalProof<N>,
    /// The network fee being paid.
    fee: u64,
    /// The signature for the request.
    signature: N::AccountSignature,
}

impl<N: Network> Request<N> {
    /// Initializes a new coinbase generation.
    pub fn new_coinbase<R: Rng + CryptoRng>(recipient: Address<N>, amount: AleoAmount, rng: &mut R) -> Result<Self> {
        let burner = PrivateKey::new(rng);
        let operation = Operation::Coinbase(recipient, amount);
        Self::new(&burner, vec![], operation, Default::default(), 0, rng)
    }

    /// Initializes a new transfer request.
    pub fn new_transfer<R: Rng + CryptoRng>(
        caller: &PrivateKey<N>,
        records: Vec<Record<N>>,
        recipient: Address<N>,
        amount: AleoAmount,
        rng: &mut R,
    ) -> Result<Self> {
        let operation = Operation::Transfer(recipient, amount);
        Self::new(caller, records, operation, Default::default(), 0, rng)
    }

    /// Signs and returns a new instance of a request.
    pub fn new<R: Rng + CryptoRng>(
        caller: &PrivateKey<N>,
        records: Vec<Record<N>>,
        operation: Operation<N>,
        ledger_proof: LedgerProof<N>,
        fee: u64,
        rng: &mut R,
    ) -> Result<Self> {
        let caller_address = Address::from_private_key(caller)?;

        // Pad the records with noops if there is less than required.
        let mut records = records;
        while records.len() < N::NUM_INPUT_RECORDS {
            records.push(Record::new_noop_input(caller_address, rng)?);
        }

        let mut commitments = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for record in records.iter().take(N::NUM_INPUT_RECORDS) {
            // Ensure the caller and record owner match.
            if caller_address != record.owner() {
                return Err(anyhow!("Address from caller private key does not match record owner"));
            }
            commitments.push(record.commitment());
        }

        let function_id = operation.function_id();
        let operation_id = operation.to_operation_id()?;
        let message = to_bytes_le![commitments /*function_id, operation_id, fee*/]?;
        let signature = caller.sign(&message, rng)?;

        Self::from(records, operation, ledger_proof, LocalProof::default(), fee, signature)
    }

    /// Returns a new instance of a noop request.
    pub fn new_noop<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng);
        let noop_address = Address::from_private_key(&noop_private_key)?;

        // Construct the noop records.
        let mut records = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            records.push(Record::new_noop_input(noop_address, rng)?);
        }

        // Set the operation and fee.
        let operation = Operation::Noop;
        let ledger_proof = LedgerProof::default();
        let fee = 0;

        Self::new(&noop_private_key, records, operation, ledger_proof, fee, rng)
    }

    /// Returns a new instance of a request.
    pub fn from(
        records: Vec<Record<N>>,
        operation: Operation<N>,
        ledger_proof: LedgerProof<N>,
        local_proof: LocalProof<N>,
        fee: u64,
        signature: N::AccountSignature,
    ) -> Result<Self> {
        let request = Self {
            records,
            operation,
            ledger_proof,
            local_proof,
            fee,
            signature,
        };

        match request.is_valid() {
            true => Ok(request),
            false => Err(anyhow!("Request is not well-formed")),
        }
    }

    /// Returns `true` if the request signature is valid.
    pub fn is_valid(&self) -> bool {
        // Ensure the number of records is correct.
        if self.records.len() != N::NUM_INPUT_RECORDS {
            eprintln!(
                "Incorrect number of request records. Expected {}, found {}",
                N::NUM_INPUT_RECORDS,
                self.records.len()
            );
            return false;
        }

        // Ensure the records contain the same owner, and retrieve the owner as the caller.
        let caller = {
            let owners: HashSet<Address<N>> = self.records.iter().map(|record| record.owner()).collect();
            if owners.len() == 1 {
                *owners.iter().next().expect("Failed to fetch request caller")
            } else {
                eprintln!("Request records do not contain the same owner");
                return false;
            }
        };

        // Ensure the records contains a total value that is at least the fee amount.
        let balance: u64 = self.records.iter().map(|record| record.value()).sum();
        if balance < self.fee {
            eprintln!("Request records do not contain sufficient value for fee");
            return false;
        }

        // Ensure the records contain at most 1 program ID, and retrieve the program ID.
        let program_id = {
            let program_id = OnceCell::new();
            for record in &self.records {
                if record.program_id() != *N::noop_program_id() {
                    if program_id.set(record.program_id()).is_err() {
                        eprintln!("Request records contains more than 1 distinct program ID");
                        return false;
                    }
                }
            }
            *program_id.get_or_init(|| *N::noop_program_id())
        };

        // If the program ID is the noop program ID, ensure the function ID is the noop function ID.
        if program_id == *N::noop_program_id() && self.function_id() != *N::noop_function_id() {
            eprintln!("Request contains mismatching program ID and function ID");
            return false;
        }

        // Ensure the function ID is in the specified program.
        {}

        // Ensure the given record commitments are in the specified ledger proof or local proof.
        {}

        // Prepare for signature verification.
        let commitments: Vec<_> = self.records.iter().map(|record| record.commitment()).collect();
        let operation_id = match self.operation.to_operation_id() {
            Ok(operation_id) => operation_id,
            Err(error) => {
                eprintln!("Failed to construct request operation ID: {:?}", error);
                return false;
            }
        };
        let message = match to_bytes_le![commitments /*self.function_id(), operation_id, self.fee*/] {
            Ok(signature_message) => signature_message,
            Err(error) => {
                eprintln!("Failed to construct request signature message: {}", error);
                return false;
            }
        };

        // Ensure the signature is valid.
        match N::account_signature_scheme().verify(&caller, &message, &self.signature) {
            Ok(is_valid) => is_valid,
            Err(error) => {
                eprintln!("Failed to verify request signature: {}", error);
                false
            }
        }
    }

    /// Returns `true` if the request calls the noop program and function.
    pub fn is_noop(&self) -> bool {
        self.to_program_id().unwrap() == *N::noop_program_id() && self.function_id() == *N::noop_function_id()
    }

    /// Returns a reference to the records.
    pub fn records(&self) -> &Vec<Record<N>> {
        &self.records
    }

    /// Returns the function ID.
    pub fn function_id(&self) -> N::FunctionID {
        self.operation.function_id()
    }

    /// Returns the function type.
    pub fn function_type(&self) -> FunctionType {
        self.operation.function_type()
    }

    /// Returns a reference to the operation.
    pub fn operation(&self) -> &Operation<N> {
        &self.operation
    }

    /// Returns the block hash used to prove inclusion of ledger-consumed records.
    pub fn block_hash(&self) -> N::BlockHash {
        self.ledger_proof.block_hash()
    }

    /// Returns a reference to the ledger proof.
    pub fn ledger_proof(&self) -> &LedgerProof<N> {
        &self.ledger_proof
    }

    /// Returns the local commitments root used to prove inclusion of locally-consumed records.
    pub fn local_commitments_root(&self) -> N::LocalCommitmentsRoot {
        self.local_proof.local_commitments_root()
    }

    /// Returns a reference to the local proof.
    pub fn local_proof(&self) -> &LocalProof<N> {
        &self.local_proof
    }

    /// Returns the fee.
    pub fn fee(&self) -> u64 {
        self.fee
    }

    /// Returns a reference to the signature.
    pub fn signature(&self) -> &N::AccountSignature {
        &self.signature
    }

    /// Returns the caller of the request.
    pub fn to_caller(&self) -> Result<Address<N>> {
        let owners: HashSet<Address<N>> = self.records.iter().map(|record| record.owner()).collect();
        match owners.len() == 1 {
            true => owners
                .into_iter()
                .next()
                .ok_or(anyhow!("Failed to retrieve the request caller")),
            false => Err(anyhow!("Request records do not contain the same owner")),
        }
    }

    /// Returns the balance of the caller.
    pub fn to_balance(&self) -> u64 {
        self.records.iter().map(|record| record.value()).sum()
    }

    /// Returns the program ID.
    pub fn to_program_id(&self) -> Result<N::ProgramID> {
        let program_id = OnceCell::new();
        for record in &self.records {
            if record.program_id() != *N::noop_program_id() {
                if program_id.set(record.program_id()).is_err() {
                    return Err(anyhow!("Request records contains more than 1 distinct program ID"));
                }
            }
        }
        Ok(*program_id.get_or_init(|| *N::noop_program_id()))
    }

    /// Returns the serial numbers.
    pub fn to_serial_numbers(&self) -> Result<Vec<N::SerialNumber>> {
        self.records
            .iter()
            .map(|record| Ok(record.to_serial_number(&ComputeKey::from_signature(&self.signature)?)?))
            .collect::<Result<Vec<_>>>()
    }

    /// Returns the input commitments.
    pub fn to_input_commitments(&self) -> Vec<N::Commitment> {
        self.records.iter().map(|record| record.commitment()).collect()
    }
}

impl<N: Network> FromBytes for Request<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut records = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            records.push(FromBytes::read_le(&mut reader)?);
        }

        let operation = FromBytes::read_le(&mut reader)?;
        let ledger_proof = FromBytes::read_le(&mut reader)?;
        let local_proof = FromBytes::read_le(&mut reader)?;
        let fee = FromBytes::read_le(&mut reader)?;
        let signature = FromBytes::read_le(&mut reader)?;

        Ok(
            Self::from(records, operation, ledger_proof, local_proof, fee, signature)
                .expect("Failed to deserialize a request"),
        )
    }
}

impl<N: Network> ToBytes for Request<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.records.write_le(&mut writer)?;
        self.operation.write_le(&mut writer)?;
        self.ledger_proof.write_le(&mut writer)?;
        self.local_proof.write_le(&mut writer)?;
        self.fee.write_le(&mut writer)?;
        self.signature.write_le(&mut writer)
    }
}

impl<N: Network> fmt::Display for Request<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::{testnet2::*, traits::account::AccountScheme, Account};
//
//     use rand::{thread_rng, SeedableRng};
//     use rand_chacha::ChaChaRng;
//
//     const ITERATIONS: usize = 100;
//
//     #[test]
//     fn test_new_noop() {
//         for _ in 0..ITERATIONS {
//             // Sample a random seed for the RNG.
//             let seed: u64 = thread_rng().gen();
//
//             // Generate the expected request state.
//             let (expected_record, expected_serial_number, expected_program_id) = {
//                 let rng = &mut ChaChaRng::seed_from_u64(seed);
//
//                 let account = Account::new(rng).unwrap();
//                 let input_record = Record::new_noop_input(account.address, rng).unwrap();
//                 let serial_number = input_record
//                     .to_serial_number(&account.private_key().to_compute_key().unwrap())
//                     .unwrap();
//                 let program_id = input_record.program_id();
//
//                 (input_record, serial_number, program_id)
//             };
//
//             // Generate the candidate request state.
//             let (candidate_record, candidate_serial_number, candidate_program_id) = {
//                 let rng = &mut ChaChaRng::seed_from_u64(seed);
//                 let input = Request::<Testnet2>::new_noop(rng).unwrap();
//                 (
//                     input.record().clone(),
//                     input.serial_number().clone(),
//                     input.program_id().clone(),
//                 )
//             };
//
//             assert_eq!(expected_record, candidate_record);
//             assert_eq!(expected_serial_number, candidate_serial_number);
//             assert_eq!(expected_program_id, candidate_program_id);
//         }
//     }
// }
