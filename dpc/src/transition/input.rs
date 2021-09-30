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
use snarkvm_algorithms::CommitmentScheme;

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct Input<N: Network> {
    record: Record<N>,
    serial_number: N::SerialNumber,
    noop_private_key: Option<PrivateKey<N>>,
}

impl<N: Network> Input<N> {
    pub fn new_noop<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng);
        let noop_compute_key = noop_private_key.to_compute_key()?;
        let noop_address = Address::from_private_key(&noop_private_key)?;

        // Construct the noop input record.
        let record = Record::new_noop_input(noop_address, rng)?;

        // Compute the serial number.
        let serial_number = record.to_serial_number(&noop_compute_key)?;

        Ok(Self {
            record,
            serial_number,
            noop_private_key: Some(noop_private_key),
        })
    }

    /// Initializes a new instance of `Input`.
    pub fn new(compute_key: &ComputeKey<N>, record: Record<N>) -> Result<Self> {
        // Ensure the account address matches.
        if Address::from_compute_key(compute_key)? != record.owner() {
            return Err(anyhow!("Address from compute key does not match the record owner"));
        }

        // Compute the serial number.
        let serial_number = record.to_serial_number(&compute_key)?;

        Ok(Self {
            record,
            serial_number,
            noop_private_key: None,
        })
    }

    /// Initializes a new instance of `Input`.
    pub fn new_full(
        compute_key: &ComputeKey<N>,
        value: AleoAmount,
        payload: Payload,
        program_id: N::ProgramID,
        serial_number_nonce: N::SerialNumber,
        commitment_randomness: <N::CommitmentScheme as CommitmentScheme>::Randomness,
    ) -> Result<Self> {
        // Derive the account address.
        let address = Address::from_compute_key(compute_key)?;

        // Construct the input record.
        let record = Record::new_input(
            address,
            value.0 as u64,
            payload,
            program_id,
            serial_number_nonce,
            commitment_randomness,
        )?;

        // Compute the serial number.
        let serial_number = record.to_serial_number(&compute_key)?;

        Ok(Self {
            record,
            serial_number,
            noop_private_key: None,
        })
    }

    /// Returns `true` if the program ID is the noop program.
    pub fn is_noop(&self) -> bool {
        self.record.program_id() == *N::noop_program_id()
    }

    /// Returns a reference to the input record.
    pub fn record(&self) -> &Record<N> {
        &self.record
    }

    /// Returns a reference to the input serial number.
    pub fn serial_number(&self) -> &N::SerialNumber {
        &self.serial_number
    }

    /// Returns a reference to the noop private key, if it exists.
    pub fn noop_private_key(&self) -> &Option<PrivateKey<N>> {
        &self.noop_private_key
    }

    /// Returns a reference to the program ID.
    pub fn program_id(&self) -> N::ProgramID {
        self.record.program_id()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::*;

    use rand::{thread_rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_new_noop() {
        for _ in 0..ITERATIONS {
            // Sample a random seed for the RNG.
            let seed: u64 = thread_rng().gen();

            // Generate the expected input state.
            let (expected_record, expected_serial_number, expected_noop_private_key, expected_program_id) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);

                let account = Account::new(rng).unwrap();
                let input_record = Record::new_noop_input(account.address, rng).unwrap();
                let serial_number = input_record
                    .to_serial_number(&account.private_key().to_compute_key().unwrap())
                    .unwrap();
                let program_id = input_record.program_id();

                (input_record, serial_number, account.private_key().clone(), program_id)
            };

            // Generate the candidate input state.
            let (candidate_record, candidate_serial_number, candidate_noop_private_key, candidate_program_id) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);
                let input = Input::<Testnet2>::new_noop(rng).unwrap();
                (
                    input.record().clone(),
                    input.serial_number().clone(),
                    input.noop_private_key().clone(),
                    input.program_id().clone(),
                )
            };

            assert_eq!(expected_record, candidate_record);
            assert_eq!(expected_serial_number, candidate_serial_number);
            assert_eq!(Some(expected_noop_private_key), candidate_noop_private_key);
            assert_eq!(expected_program_id, candidate_program_id);
        }
    }
}
