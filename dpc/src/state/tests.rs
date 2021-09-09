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

mod coinbase {
    use crate::{prelude::*, testnet2::*};
    use snarkvm_utilities::ToBytes;

    use rand::{thread_rng, Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_new_coinbase() {
        for _ in 0..ITERATIONS {
            // Sample a random seed for the RNG.
            let seed: u64 = thread_rng().gen();

            // Generate the expected state transition.
            let (expected_account, expected_record, expected_joint_serial_numbers) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);

                // Generate the expected coinbase account.
                let coinbase_account = Account::<Testnet2Parameters>::new(rng).unwrap();

                // Compute the padded inputs to keep the RNG in sync.
                let mut inputs = Vec::with_capacity(Testnet2Parameters::NUM_INPUT_RECORDS);
                let mut joint_serial_numbers = Vec::with_capacity(Testnet2Parameters::NUM_INPUT_RECORDS);
                for _ in 0..Testnet2Parameters::NUM_INPUT_RECORDS {
                    let input = Input::<Testnet2Parameters>::new_noop(rng).unwrap();
                    joint_serial_numbers.extend_from_slice(&input.serial_number().to_bytes_le().unwrap());
                    inputs.push(input);
                }

                // Compute the remaining padded outputs to keep the RNG in sync.
                let mut outputs = Vec::with_capacity(Testnet2Parameters::NUM_OUTPUT_RECORDS);
                for _ in 0..Testnet2Parameters::NUM_OUTPUT_RECORDS - 1 {
                    outputs.push(Output::<Testnet2Parameters>::new_noop(rng).unwrap());
                }

                // Generate the expected coinbase record.
                let coinbase_record = {
                    Record::new_output(
                        Testnet2Parameters::noop_program().program_id(),
                        coinbase_account.address,
                        false,
                        123456,
                        Payload::default(),
                        Testnet2Parameters::NUM_INPUT_RECORDS as u8,
                        &joint_serial_numbers,
                        rng,
                    )
                    .unwrap()
                };

                (coinbase_account, coinbase_record, joint_serial_numbers)
            };

            // Generate the candidate state transition.
            let (candidate_account, candidate_state, candidate_joint_serial_numbers) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);

                let account = Account::new(rng).unwrap();
                let state =
                    StateTransition::new_coinbase(account.address, AleoAmount::from_bytes(123456), rng).unwrap();
                let joint_serial_numbers = state.kernel().to_joint_serial_numbers().unwrap();

                (account, state, joint_serial_numbers)
            };

            assert_eq!(expected_account.address, candidate_account.address);
            for i in 0..Testnet2Parameters::NUM_INPUT_RECORDS {
                assert!(candidate_state.input_records()[i].is_dummy());
            }
            for j in 1..Testnet2Parameters::NUM_OUTPUT_RECORDS {
                assert!(candidate_state.output_records()[j].is_dummy());
            }
            assert_eq!(expected_joint_serial_numbers, candidate_joint_serial_numbers);
            assert_eq!(expected_record, candidate_state.output_records()[0].clone());
        }
    }
}
