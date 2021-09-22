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

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::convert::TryInto;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct Output<N: Network> {
    address: Address<N>,
    value: AleoAmount,
    payload: Payload,
    executable: Executable<N>,
}

impl<N: Network> Output<N> {
    pub fn new_noop<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng);
        let noop_address = noop_private_key.try_into()?;

        Self::new(noop_address, AleoAmount::from_bytes(0), Payload::default(), None)
    }

    /// Initializes a new instance of `Output`.
    pub fn new(
        address: Address<N>,
        value: AleoAmount,
        payload: Payload,
        executable: Option<Executable<N>>,
    ) -> Result<Self> {
        // Retrieve the executable. If `None` is provided, construct the noop executable.
        let executable = match executable {
            Some(executable) => executable,
            None => Executable::Noop,
        };

        Ok(Self {
            address,
            value,
            payload,
            executable,
        })
    }

    /// Returns the output record, given the previous serial number.
    pub fn to_record<R: Rng + CryptoRng>(
        &self,
        serial_number_nonce: N::SerialNumber,
        rng: &mut R,
    ) -> Result<Record<N>> {
        // Determine if the record is a dummy.
        let is_dummy = self.value == AleoAmount::from_bytes(0) && self.payload.is_empty() && self.executable.is_noop();

        Ok(Record::new_output(
            self.address,
            is_dummy,
            self.value.0 as u64,
            self.payload.clone(),
            self.executable.program_id(),
            serial_number_nonce,
            rng,
        )?)
    }

    /// Returns the address.
    pub fn address(&self) -> Address<N> {
        self.address
    }

    /// Returns the value.
    pub fn value(&self) -> AleoAmount {
        self.value
    }

    /// Returns a reference to the payload.
    pub fn payload(&self) -> &Payload {
        &self.payload
    }

    /// Returns a reference to the executable.
    pub fn executable(&self) -> &Executable<N> {
        &self.executable
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
    fn test_new_noop_and_to_record() {
        for _ in 0..ITERATIONS {
            // Sample a random seed for the RNG.
            let seed: u64 = thread_rng().gen();

            // Generate the given inputs.
            let mut given_rng = ChaChaRng::seed_from_u64(seed);
            let given_serial_numbers = {
                let mut serial_numbers = Vec::with_capacity(Testnet2::NUM_INPUT_RECORDS);
                for _ in 0..Testnet2::NUM_INPUT_RECORDS {
                    let input = Input::<Testnet2>::new_noop(&mut given_rng).unwrap();
                    serial_numbers.push(input.serial_number().clone());
                }
                serial_numbers
            };

            // Checkpoint the RNG and clone it.
            let mut expected_rng = given_rng.clone();
            let mut candidate_rng = given_rng.clone();

            // Generate the expected output state.
            let expected_record = {
                let account = Account::<Testnet2>::new(&mut expected_rng).unwrap();
                Record::new_noop_output(account.address, given_serial_numbers[0], &mut expected_rng).unwrap()
            };

            // Generate the candidate output state.
            let (candidate_record, candidate_address, candidate_value, candidate_payload, candidate_executable) = {
                let output = Output::new_noop(&mut candidate_rng).unwrap();
                let record = output.to_record(given_serial_numbers[0], &mut candidate_rng).unwrap();
                (
                    record,
                    output.address(),
                    output.value(),
                    output.payload().clone(),
                    output.executable().clone(),
                )
            };

            assert_eq!(expected_record, candidate_record);
            assert_eq!(expected_record.owner(), candidate_address);
            assert_eq!(expected_record.value(), candidate_value.0 as u64);
            assert_eq!(expected_record.payload(), &candidate_payload);
            assert!(candidate_executable.is_noop());
        }
    }
}
