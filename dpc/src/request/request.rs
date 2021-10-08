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

use crate::{Address, Network, PrivateKey, Record};
use snarkvm_algorithms::SignatureScheme;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::{
    fmt::{
        Display, Formatter, {self},
    },
    io::{Read, Result as IoResult, Write},
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Request<N: Network> {
    /// The program being invoked.
    program_id: N::ProgramID,
    /// The program records being invoked.
    program_records: Vec<Record<N>>,
    /// The function being called.
    function_id: N::FunctionID,
    /// The function inputs.
    function_inputs: Vec<N::InnerScalarField>,
    /// The prover requested for the execution.
    prover: Address<N>,
    /// The prover fee for the execution.
    prover_fee: u64,
    /// The signatures for the request.
    signatures: Vec<N::AccountSignature>,
}

impl<N: Network> Request<N> {
    // /// Returns the
    // pub fn to_serial_numbers(&self) -> Result<Vec<N::SerialNumber>> {
    //     self.records.to_serial_number(&caller.to_compute_key()?)?;
    //
    // }

    // /// The serial number of the record being consumed.
    // serial_number: N::SerialNumber,

    // /// The digest of the inputs from this caller.
    // inputs_digest: N::FunctionInputsDigest,

    /// Signs and returns a new instance of an input.
    pub fn new<R: Rng + CryptoRng>(
        caller: &PrivateKey<N>,
        program_id: N::ProgramID,
        function_id: N::FunctionID,
        inputs: Vec<N::InnerScalarField>,
        record: Record<N>,
        inputs_digest: N::FunctionInputsDigest,
        fee: u64,
        rng: &mut R,
    ) -> Result<Self> {
        // Ensure the caller and record owner match.
        if Address::from_private_key(caller)? != record.owner() {
            return Err(anyhow!("Address from caller private key does not match record owner"));
        }

        // Construct and sign the input.
        let serial_number = record.to_serial_number(&caller.to_compute_key()?)?;
        let message = to_bytes_le![serial_number, program_id, function_id, inputs_digest, fee]?;
        let signature = caller.sign(&message, rng)?;
        Self::from(
            record,
            serial_number,
            program_id,
            function_id,
            inputs_digest,
            fee,
            signature,
        )
    }

    /// Returns a new instance of a noop input.
    pub fn new_noop<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng);
        let noop_compute_key = noop_private_key.to_compute_key()?;
        let noop_address = Address::from_private_key(&noop_private_key)?;

        // Construct the noop input parameters.
        let record = Record::new_noop_input(noop_address, rng)?;
        let serial_number = record.to_serial_number(&noop_compute_key)?;
        let program_id = *N::noop_program_id();
        let circuit_id = *N::noop_circuit_id();
        let inputs_digest = N::FunctionInputsDigest::default();
        let fee = 0;

        // Construct and sign the input.
        let message = to_bytes_le![serial_number, program_id, circuit_id, inputs_digest, fee]?;
        let signature = noop_private_key.sign(&message, rng)?;
        Self::from(
            record,
            serial_number,
            program_id,
            circuit_id,
            inputs_digest,
            fee,
            signature,
        )
    }

    /// Returns a new instance of an input.
    pub fn from(
        record: Record<N>,
        serial_number: N::SerialNumber,
        program_id: N::ProgramID,
        function_id: N::FunctionID,
        inputs: Vec<N::InnerScalarField>,
        inputs_digest: N::FunctionInputsDigest,
        fee: u64,
        signature: N::AccountSignature,
    ) -> Result<Self> {
        let input = Self {
            program_id,
            function_id,
            program_records: record,
            serial_number,
            inputs_digest,
            prover_fee: fee,
            signature,
        };

        match input.is_valid() {
            true => Ok(input),
            false => Err(anyhow!("Input is not well-formed")),
        }
    }

    /// Returns `true` if the input signature is valid.
    pub fn is_valid(&self) -> bool {
        let message = match to_bytes_le![
            self.serial_number,
            self.program_id,
            self.function_id,
            self.inputs_digest,
            self.prover_fee
        ] {
            Ok(signature_message) => signature_message,
            Err(error) => {
                eprintln!("Failed to construct input signature message: {}", error);
                return false;
            }
        };

        match N::account_signature_scheme().verify(&self.program_records.owner(), &message, &self.signature) {
            Ok(is_valid) => is_valid,
            Err(error) => {
                eprintln!("Failed to verify input signature: {}", error);
                return false;
            }
        }
    }

    /// Returns `true` if the program ID is the noop program.
    pub fn is_noop(&self) -> bool {
        self.program_records.program_id() == *N::noop_program_id() && self.function_id == *N::noop_circuit_id()
    }

    /// Returns a reference to the input record.
    pub fn record(&self) -> &Record<N> {
        &self.program_records
    }

    /// Returns the program ID.
    pub fn program_id(&self) -> N::ProgramID {
        self.program_id
    }

    /// Returns the function ID.
    pub fn function_id(&self) -> N::FunctionID {
        self.function_id
    }

    /// Returns a reference to the input serial number.
    pub fn serial_number(&self) -> &N::SerialNumber {
        &self.serial_number
    }

    /// Returns the fee.
    pub fn fee(&self) -> u64 {
        self.prover_fee
    }

    /// Returns a reference to the signature.
    pub fn signature(&self) -> &N::AccountSignature {
        &self.signature
    }
}

impl<N: Network> FromBytes for Request<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let program_id = FromBytes::read_le(&mut reader)?;
        let function_id = FromBytes::read_le(&mut reader)?;
        let record = FromBytes::read_le(&mut reader)?;
        let serial_number = FromBytes::read_le(&mut reader)?;
        let inputs_digest = FromBytes::read_le(&mut reader)?;
        let fee = FromBytes::read_le(&mut reader)?;
        let signature = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(
            record,
            serial_number,
            program_id,
            function_id,
            inputs_digest,
            fee,
            signature,
        )
        .expect("Failed to deserialize an input"))
    }
}

impl<N: Network> ToBytes for Request<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.program_id.write_le(&mut writer)?;
        self.function_id.write_le(&mut writer)?;
        self.program_records.write_le(&mut writer)?;
        self.serial_number.write_le(&mut writer)?;
        self.inputs_digest.write_le(&mut writer)?;
        self.prover_fee.write_le(&mut writer)?;
        self.signature.write_le(&mut writer)
    }
}

impl<N: Network> Display for Request<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{testnet2::*, traits::account::AccountScheme, Account};

    use rand::{thread_rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_new_noop() {
        for _ in 0..ITERATIONS {
            // Sample a random seed for the RNG.
            let seed: u64 = thread_rng().gen();

            // Generate the expected request state.
            let (expected_record, expected_serial_number, expected_program_id) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);

                let account = Account::new(rng).unwrap();
                let input_record = Record::new_noop_input(account.address, rng).unwrap();
                let serial_number = input_record
                    .to_serial_number(&account.private_key().to_compute_key().unwrap())
                    .unwrap();
                let program_id = input_record.program_id();

                (input_record, serial_number, program_id)
            };

            // Generate the candidate request state.
            let (candidate_record, candidate_serial_number, candidate_program_id) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);
                let input = Request::<Testnet2>::new_noop(rng).unwrap();
                (
                    input.record().clone(),
                    input.serial_number().clone(),
                    input.program_id().clone(),
                )
            };

            assert_eq!(expected_record, candidate_record);
            assert_eq!(expected_serial_number, candidate_serial_number);
            assert_eq!(expected_program_id, candidate_program_id);
        }
    }
}
