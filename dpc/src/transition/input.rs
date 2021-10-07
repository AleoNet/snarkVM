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
        Display,
        Formatter,
        {self},
    },
    io::{Read, Result as IoResult, Write},
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Input<N: Network> {
    /// The record being consumed.
    record: Record<N>,
    /// The serial number of the record being consumed.
    serial_number: N::SerialNumber,
    /// The program function being called.
    circuit_id: N::ProgramCircuitID,
    /// The digest of the inputs from this caller.
    inputs_digest: N::InnerScalarField,
    /// The fee amount this caller is contributing.
    fee: u64,
    /// The signature for this input.
    signature: N::AccountSignature,
}

impl<N: Network> Input<N> {
    /// Signs and returns a new instance of an input.
    pub fn new<R: Rng + CryptoRng>(
        caller: &PrivateKey<N>,
        record: Record<N>,
        circuit_id: N::ProgramCircuitID,
        inputs_digest: N::InnerScalarField,
        fee: u64,
        rng: &mut R,
    ) -> Result<Self> {
        // Ensure the caller and record owner match.
        if Address::from_private_key(caller)? != record.owner() {
            return Err(anyhow!("Address from caller private key does not match record owner"));
        }

        // Construct and sign the input.
        let serial_number = record.to_serial_number(&caller.to_compute_key()?)?;
        let message = to_bytes_le![serial_number, circuit_id, inputs_digest, fee]?;
        let signature = caller.sign(&message, rng)?;
        Self::from(record, serial_number, circuit_id, inputs_digest, fee, signature)
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
        let circuit_id = *N::noop_circuit_id();
        let inputs_digest = N::InnerScalarField::default();
        let fee = 0;

        // Construct and sign the input.
        let message = to_bytes_le![serial_number, circuit_id, inputs_digest, fee]?;
        let signature = noop_private_key.sign(&message, rng)?;
        Self::from(record, serial_number, circuit_id, inputs_digest, fee, signature)
    }

    /// Returns a new instance of an input.
    pub fn from(
        record: Record<N>,
        serial_number: N::SerialNumber,
        circuit_id: N::ProgramCircuitID,
        inputs_digest: N::InnerScalarField,
        fee: u64,
        signature: N::AccountSignature,
    ) -> Result<Self> {
        let input = Self {
            record,
            serial_number,
            circuit_id,
            inputs_digest,
            fee,
            signature,
        };

        match input.is_valid() {
            true => Ok(input),
            false => Err(anyhow!("Input is not well-formed")),
        }
    }

    /// Returns `true` if the input signature is valid.
    pub fn is_valid(&self) -> bool {
        let message = match to_bytes_le![self.serial_number, self.circuit_id, self.inputs_digest, self.fee] {
            Ok(signature_message) => signature_message,
            Err(error) => {
                eprintln!("Failed to construct input signature message: {}", error);
                return false;
            }
        };

        match N::account_signature_scheme().verify(&self.record.owner(), &message, &self.signature) {
            Ok(is_valid) => is_valid,
            Err(error) => {
                eprintln!("Failed to verify input signature: {}", error);
                return false;
            }
        }
    }

    /// Returns `true` if the program ID is the noop program.
    pub fn is_noop(&self) -> bool {
        self.record.program_id() == *N::noop_program_id() && self.circuit_id == *N::noop_circuit_id()
    }

    /// Returns a reference to the input record.
    pub fn record(&self) -> &Record<N> {
        &self.record
    }

    /// Returns the program ID.
    pub fn program_id(&self) -> N::ProgramID {
        self.record.program_id()
    }

    /// Returns the circuit ID.
    pub fn circuit_id(&self) -> N::ProgramCircuitID {
        self.circuit_id
    }

    /// Returns a reference to the input serial number.
    pub fn serial_number(&self) -> &N::SerialNumber {
        &self.serial_number
    }

    /// Returns the fee.
    pub fn fee(&self) -> u64 {
        self.fee
    }

    /// Returns a reference to the signature.
    pub fn signature(&self) -> &N::AccountSignature {
        &self.signature
    }
}

impl<N: Network> FromBytes for Input<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let record = FromBytes::read_le(&mut reader)?;
        let serial_number = FromBytes::read_le(&mut reader)?;
        let circuit_id = FromBytes::read_le(&mut reader)?;
        let inputs_digest = FromBytes::read_le(&mut reader)?;
        let fee = FromBytes::read_le(&mut reader)?;
        let signature = FromBytes::read_le(&mut reader)?;

        Ok(
            Self::from(record, serial_number, circuit_id, inputs_digest, fee, signature)
                .expect("Failed to deserialize an input"),
        )
    }
}

impl<N: Network> ToBytes for Input<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.record.write_le(&mut writer)?;
        self.serial_number.write_le(&mut writer)?;
        self.circuit_id.write_le(&mut writer)?;
        self.inputs_digest.write_le(&mut writer)?;
        self.fee.write_le(&mut writer)?;
        self.signature.write_le(&mut writer)
    }
}

impl<N: Network> Display for Input<N> {
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

            // Generate the expected input state.
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

            // Generate the candidate input state.
            let (candidate_record, candidate_serial_number, candidate_program_id) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);
                let input = Input::<Testnet2>::new_noop(rng).unwrap();
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
