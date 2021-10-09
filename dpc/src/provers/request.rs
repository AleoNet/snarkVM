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

use crate::{Address, ComputeKey, Function, FunctionInputs, Network, Noop, PrivateKey, Program, Record};
use snarkvm_algorithms::{CryptoHash, SignatureScheme};
use snarkvm_fields::ToConstraintField;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use std::{
    fmt::{
        Display, Formatter, {self},
    },
    io::{Read, Result as IoResult, Write},
};

/**

Function {
    program_id,
    merkle_path,
    function_id, := Hash(function_type || IR)
    IR
}
*/
pub enum Operation<N: Network> {
    /// Noop.
    Noop,
    /// Mints the given amount to the recipient address.
    Coinbase(Address<N>, u64),
    /// Transfers the given amount to the recipient address.
    Transfer(Vec<Record<N>>, Address<N>, u64),
    /// Deploys the given program.
    Deploy(Vec<Record<N>>, N::ProgramID, Program<N>),
    /// Invokes the given records on the function and inputs.
    Function(Vec<Record<N>>, N::ProgramID, N::FunctionID, FunctionInputs<N>),
}

#[derive(Clone, Debug)]
pub struct Request<N: Network> {
    /// The records being consumed.
    records: Vec<Record<N>>,
    /// The program being invoked.
    program_id: N::ProgramID,
    /// The function being called.
    function_id: N::FunctionID,
    /// The function inputs being provided.
    inputs: FunctionInputs<N>,
    /// The network fee being paid.
    fees: Vec<u64>,
    /// The signatures for the request.
    signatures: Vec<N::AccountSignature>,
}

impl<N: Network> Request<N> {
    /// Signs and returns a new instance of a request.
    pub fn new<R: Rng + CryptoRng>(
        callers: &Vec<PrivateKey<N>>,
        records: Vec<Record<N>>,
        program_id: N::ProgramID,
        function_id: N::FunctionID,
        inputs: FunctionInputs<N>,
        fees: Vec<u64>,
        rng: &mut R,
    ) -> Result<Self> {
        let inputs_digest = N::FunctionInputsCRH::evaluate(&inputs.to_field_elements()?)?;
        let mut signatures = Vec::with_capacity(N::NUM_INPUT_RECORDS);

        for ((caller, record), fee) in callers.iter().zip_eq(records.iter()).zip_eq(fees.iter()) {
            // Ensure the caller and record owner match.
            if Address::from_private_key(caller)? != record.owner() {
                return Err(anyhow!("Address from caller private key does not match record owner"));
            }

            // Construct and sign the request.
            let commitment = record.commitment();
            let message = to_bytes_le![commitment, program_id, function_id, inputs_digest, fee]?;
            let signature = caller.sign(&message, rng)?;
            signatures.push(signature);
        }

        Self::from(records, program_id, function_id, inputs, fees, signatures)
    }

    /// Returns a new instance of a noop request.
    pub fn new_noop<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng);
        let noop_address = Address::from_private_key(&noop_private_key)?;

        // Fetch the noop program, function, inputs, and fee.
        let program_id = *N::noop_program_id();
        let noop = Noop::<N>::new();
        let function_id = noop.function_id();
        let inputs_digest = N::FunctionInputsDigest::default();
        let fee = 0;

        // Construct the noop request parameters.
        let mut records = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        let mut signatures = Vec::with_capacity(N::NUM_INPUT_RECORDS);

        for _ in 0..N::NUM_INPUT_RECORDS {
            let record = Record::new_noop_input(noop_address, rng)?;
            let commitment = record.commitment();
            let message = to_bytes_le![commitment, program_id, function_id, inputs_digest, fee]?;
            let signature = noop_private_key.sign(&message, rng)?;

            records.push(record);
            signatures.push(signature);
        }

        Self::from(
            records,
            program_id,
            function_id,
            FunctionInputs::default(),
            vec![fee, fee],
            signatures,
        )
    }

    /// Returns a new instance of a request.
    pub fn from(
        records: Vec<Record<N>>,
        program_id: N::ProgramID,
        function_id: N::FunctionID,
        inputs: FunctionInputs<N>,
        fees: Vec<u64>,
        signatures: Vec<N::AccountSignature>,
    ) -> Result<Self> {
        let request = Self {
            records,
            program_id,
            function_id,
            inputs,
            fees,
            signatures,
        };

        match request.is_valid() {
            true => Ok(request),
            false => Err(anyhow!("Request is not well-formed")),
        }
    }

    /// Returns `true` if the request signature is valid.
    pub fn is_valid(&self) -> bool {
        let inputs_digest = match self.to_inputs_digest() {
            Ok(digest) => digest,
            Err(error) => {
                eprintln!("Failed to construct request function inputs digest: {:?}", error);
                return false;
            }
        };

        for ((record, fee), signature) in self
            .records
            .iter()
            .zip_eq(self.fees.iter())
            .zip_eq(self.signatures.iter())
        {
            // Ensure the record contains at least minimum required fee amount.
            if record.value() < *fee {
                eprintln!("Request record does not contain sufficient value for fee");
                return false;
            }

            // Ensure the signature is valid.
            let commitment = record.commitment();
            let message = match to_bytes_le![commitment, self.program_id, self.function_id, inputs_digest, fee] {
                Ok(signature_message) => signature_message,
                Err(error) => {
                    eprintln!("Failed to construct request signature message: {}", error);
                    return false;
                }
            };
            match N::account_signature_scheme().verify(&record.owner(), &message, &signature) {
                Ok(is_valid) => {
                    if !is_valid {
                        eprintln!("Request signature is invalid");
                        return false;
                    }
                }
                Err(error) => {
                    eprintln!("Failed to verify input signature: {}", error);
                    return false;
                }
            }
        }
        true
    }

    /// Returns `true` if the request calls the noop program and function.
    pub fn is_noop(&self) -> bool {
        self.program_id == *N::noop_program_id() && self.function_id == *N::noop_circuit_id()
    }

    /// Returns a reference to the records.
    pub fn records(&self) -> &Vec<Record<N>> {
        &self.records
    }

    /// Returns the program ID.
    pub fn program_id(&self) -> N::ProgramID {
        self.program_id
    }

    /// Returns the function ID.
    pub fn function_id(&self) -> N::FunctionID {
        self.function_id
    }

    /// Returns a reference to the function inputs.
    pub fn inputs(&self) -> &FunctionInputs<N> {
        &self.inputs
    }

    /// Returns a reference to the fees.
    pub fn fees(&self) -> &Vec<u64> {
        &self.fees
    }

    /// Returns a reference to the signatures.
    pub fn signatures(&self) -> &Vec<N::AccountSignature> {
        &self.signatures
    }

    /// Returns a digest of the function inputs.
    pub fn to_inputs_digest(&self) -> Result<N::FunctionInputsDigest> {
        Ok(N::FunctionInputsCRH::evaluate(&self.inputs.to_field_elements()?)?)
    }

    /// Returns the serial numbers.
    pub fn to_serial_numbers(&self) -> Result<Vec<N::SerialNumber>> {
        self.records
            .iter()
            .zip_eq(self.signatures.iter())
            .map(|(record, signature)| Ok(record.to_serial_number(&ComputeKey::from_signature(signature)?)?))
            .collect::<Result<Vec<_>>>()
    }
}

impl<N: Network> FromBytes for Request<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut records = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            records.push(FromBytes::read_le(&mut reader)?);
        }

        let program_id = FromBytes::read_le(&mut reader)?;
        let function_id = FromBytes::read_le(&mut reader)?;
        let inputs = FromBytes::read_le(&mut reader)?;

        let mut fees = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            fees.push(FromBytes::read_le(&mut reader)?);
        }

        let mut signatures = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            signatures.push(FromBytes::read_le(&mut reader)?);
        }

        Ok(Self::from(records, program_id, function_id, inputs, fees, signatures)
            .expect("Failed to deserialize a request"))
    }
}

impl<N: Network> ToBytes for Request<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.records.write_le(&mut writer)?;
        self.program_id.write_le(&mut writer)?;
        self.function_id.write_le(&mut writer)?;
        self.inputs.write_le(&mut writer)?;
        self.fees.write_le(&mut writer)?;
        self.signatures.write_le(&mut writer)
    }
}

impl<N: Network> Display for Request<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
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
