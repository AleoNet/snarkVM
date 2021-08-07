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
use snarkvm_algorithms::{CommitmentScheme, SignatureScheme};

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::sync::Arc;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct Input<C: Parameters> {
    executable: Executable<C>,
    record: Record<C>,
    serial_number: C::AccountSignaturePublicKey,
    randomized_private_key: <C::AccountSignatureScheme as SignatureScheme>::RandomizedPrivateKey,
}

impl<C: Parameters> Input<C> {
    /// TODO (howardwu): TEMPORARY - `noop: Arc<NoopProgram<C>>` will be removed when `DPC::setup` and `DPC::load` are refactored.
    pub fn new_noop<R: Rng + CryptoRng>(noop: Arc<NoopProgram<C>>, rng: &mut R) -> Result<Self> {
        // Construct the noop executable.
        let executable = Executable::Noop(noop);

        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng)?;
        let noop_address = Address::from_private_key(&noop_private_key)?;

        // Construct the noop input record.
        let record = Record::new_noop_input(executable.program(), noop_address, rng)?;

        // Compute the serial number.
        let (serial_number, signature_randomizer) = record.to_serial_number(&noop_private_key)?;

        // Randomize the private key.
        let randomized_private_key =
            C::account_signature_scheme().randomize_private_key(&noop_private_key.sk_sig, &signature_randomizer)?;

        Ok(Self {
            executable,
            record,
            serial_number,
            randomized_private_key,
        })
    }

    /// Initializes a new instance of `Input`.
    pub fn new(
        private_key: PrivateKey<C>,
        executable: Executable<C>,
        is_dummy: bool,
        value: u64,
        payload: Payload,
        serial_number_nonce: C::SerialNumberNonce,
        commitment_randomness: <C::RecordCommitmentScheme as CommitmentScheme>::Randomness,
    ) -> Result<Self> {
        // Derive the account address.
        let address = Address::from_private_key(&private_key)?;

        // Construct the input record.
        let record = Record::new_input(
            executable.program(),
            address,
            is_dummy,
            value,
            payload,
            serial_number_nonce,
            commitment_randomness,
        )?;

        // Compute the serial number.
        let (serial_number, signature_randomizer) = record.to_serial_number(&private_key)?;

        // Randomize the private key.
        let randomized_private_key =
            C::account_signature_scheme().randomize_private_key(&private_key.sk_sig, &signature_randomizer)?;

        Ok(Self {
            executable,
            record,
            serial_number,
            randomized_private_key,
        })
    }

    /// Returns a reference to the input serial number.
    pub fn serial_number(&self) -> &C::AccountSignaturePublicKey {
        &self.serial_number
    }
}
