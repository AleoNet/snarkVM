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

use crate::{Address, Network, PrivateKey};
use snarkvm_algorithms::SignatureScheme;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::{
    convert::TryInto,
    fmt::{
        Display,
        Formatter,
        {self},
    },
    io::{Read, Result as IoResult, Write},
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Invocation<N: Network> {
    /// The originator of this invocation.
    caller: Address<N>,
    /// The serial number of the record being spent.
    serial_number: N::SerialNumber,
    /// The program function being called.
    circuit_id: N::ProgramCircuitID,
    /// The digest of the inputs from this caller.
    inputs_hash: N::InnerScalarField,
    /// The fee amount this caller is contributing.
    fee: u64,
    /// The signature of this invocation.
    signature: N::AccountSignature,
}

impl<N: Network> Invocation<N> {
    /// Signs and returns a new instance of an invocation.
    pub fn new<R: Rng + CryptoRng>(
        caller: PrivateKey<N>,
        serial_number: N::SerialNumber,
        circuit_id: N::ProgramCircuitID,
        inputs_hash: N::InnerScalarField,
        fee: u64,
        rng: &mut R,
    ) -> Result<Self> {
        let message = to_bytes_le![serial_number, circuit_id, inputs_hash, fee]?;
        let signature = caller.sign(&message, rng)?;

        Self::from(
            caller.try_into()?,
            serial_number,
            circuit_id,
            inputs_hash,
            fee,
            signature,
        )
    }

    /// Returns a new instance of a noop invocation.
    pub fn new_noop<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng);

        // Construct the noop invocation parameters.
        let serial_number = N::SerialNumber::default();
        let circuit_id = *N::noop_circuit_id();
        let inputs_hash = N::InnerScalarField::default();
        let fee = 0;

        // Construct and sign a noop signature.
        let message = to_bytes_le![serial_number, circuit_id, inputs_hash, fee]?;
        let signature = noop_private_key.sign(&message, rng)?;

        Self::from(
            noop_private_key.try_into()?,
            serial_number,
            circuit_id,
            inputs_hash,
            fee,
            signature,
        )
    }

    /// Returns a new instance of an invocation.
    pub fn from(
        caller: Address<N>,
        serial_number: N::SerialNumber,
        circuit_id: N::ProgramCircuitID,
        inputs_hash: N::InnerScalarField,
        fee: u64,
        signature: N::AccountSignature,
    ) -> Result<Self> {
        let invocation = Self {
            caller,
            serial_number,
            circuit_id,
            inputs_hash,
            fee,
            signature,
        };

        match invocation.is_valid() {
            true => Ok(invocation),
            false => Err(anyhow!("Invocation is invalid")),
        }
    }

    /// Returns `true` if the invocation signature is valid.
    pub fn is_valid(&self) -> bool {
        let message = match to_bytes_le![self.serial_number, self.circuit_id, self.inputs_hash, self.fee] {
            Ok(signature_message) => signature_message,
            Err(error) => {
                eprintln!("Failed to construct invocation signature message: {}", error);
                return false;
            }
        };

        match N::account_signature_scheme().verify(&self.caller, &message, &self.signature) {
            Ok(is_valid) => is_valid,
            Err(error) => {
                eprintln!("Failed to verify invocation signature: {}", error);
                return false;
            }
        }
    }
}

impl<N: Network> FromBytes for Invocation<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let caller = FromBytes::read_le(&mut reader)?;
        let serial_number = FromBytes::read_le(&mut reader)?;
        let circuit_id = FromBytes::read_le(&mut reader)?;
        let inputs_hash = FromBytes::read_le(&mut reader)?;
        let fee = FromBytes::read_le(&mut reader)?;
        let signature = FromBytes::read_le(&mut reader)?;

        Ok(
            Self::from(caller, serial_number, circuit_id, inputs_hash, fee, signature)
                .expect("Failed to deserialize an invocation"),
        )
    }
}

impl<N: Network> ToBytes for Invocation<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.caller.write_le(&mut writer)?;
        self.serial_number.write_le(&mut writer)?;
        self.circuit_id.write_le(&mut writer)?;
        self.inputs_hash.write_le(&mut writer)?;
        self.fee.write_le(&mut writer)?;
        self.signature.write_le(&mut writer)
    }
}

impl<N: Network> Display for Invocation<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
