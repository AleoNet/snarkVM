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

    use rand::{thread_rng, Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_new_coinbase() {
        for _ in 0..ITERATIONS {
            // Sample a random seed for the RNG.
            let seed: u64 = thread_rng().gen();

            // Generate the expected state transition.
            let (expected_account, expected_record, expected_serial_numbers) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);

                // Generate the expected coinbase account.
                let coinbase_account = Account::<Testnet2>::new(rng).unwrap();

                // Compute the padded inputs to keep the RNG in sync.
                let mut inputs = Vec::with_capacity(Testnet2::NUM_INPUT_RECORDS);
                let mut serial_numbers = Vec::with_capacity(Testnet2::NUM_INPUT_RECORDS);
                for _ in 0..Testnet2::NUM_INPUT_RECORDS {
                    let input = Input::<Testnet2>::new_noop(rng).unwrap();
                    serial_numbers.push(input.serial_number().clone());
                    inputs.push(input);
                }

                // Compute the remaining padded outputs to keep the RNG in sync.
                let mut outputs = Vec::with_capacity(Testnet2::NUM_OUTPUT_RECORDS);
                for _ in 0..Testnet2::NUM_OUTPUT_RECORDS - 1 {
                    outputs.push(Output::<Testnet2>::new_noop(rng).unwrap());
                }

                // Generate the expected coinbase record.
                let coinbase_record = {
                    Record::new_output(
                        Testnet2::noop_program().program_id(),
                        coinbase_account.address,
                        false,
                        123456,
                        Payload::default(),
                        serial_numbers[0],
                        rng,
                    )
                    .unwrap()
                };

                (coinbase_account, coinbase_record, serial_numbers)
            };

            // Generate the candidate state transition.
            let (candidate_account, candidate_state, candidate_serial_numbers) = {
                let rng = &mut ChaChaRng::seed_from_u64(seed);

                let account = Account::new(rng).unwrap();
                let state =
                    StateTransition::new_coinbase(account.address, AleoAmount::from_bytes(123456), rng).unwrap();
                let serial_numbers = state.kernel().serial_numbers().clone();

                (account, state, serial_numbers)
            };

            assert_eq!(expected_account.address, candidate_account.address);
            for i in 0..Testnet2::NUM_INPUT_RECORDS {
                assert!(candidate_state.input_records()[i].is_dummy());
            }
            for j in 1..Testnet2::NUM_OUTPUT_RECORDS {
                assert!(candidate_state.output_records()[j].is_dummy());
            }
            assert_eq!(expected_serial_numbers, candidate_serial_numbers);
            assert_eq!(expected_record, candidate_state.output_records()[0].clone());
        }
    }
}

mod transfer {
    use crate::{prelude::*, testnet2::*};

    use rand::{thread_rng, Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    #[test]
    fn test_new_transfer() {
        // Generate a coinbase record.
        let sender = Account::<Testnet2>::new(&mut thread_rng()).unwrap();
        let amount = AleoAmount::from_bytes(123456);
        let coinbase_record = {
            let state_transition = StateTransition::new_coinbase(sender.address, amount, &mut thread_rng()).unwrap();
            state_transition.output_records()[0].clone()
        };
        assert_eq!(coinbase_record.owner(), sender.address);
        assert_eq!(coinbase_record.value() as i64, amount.0);

        // Sample random seed for the RNG.
        let seed: u64 = thread_rng().gen();

        // Generate the expected state transition.
        let (expected_recipient, expected_sender_record, expected_recipient_record, expected_serial_numbers) = {
            let rng = &mut ChaChaRng::seed_from_u64(seed);
            let recipient = Account::new(rng).unwrap();

            // Generate sender input
            let sender_input = Input::new(
                &sender.private_key().to_compute_key().unwrap(),
                coinbase_record.clone(),
                Some(Executable::Noop),
            )
            .unwrap();

            let mut inputs = Vec::with_capacity(Testnet2::NUM_INPUT_RECORDS);
            let mut serial_numbers = Vec::with_capacity(Testnet2::NUM_INPUT_RECORDS);

            serial_numbers.push(sender_input.serial_number().clone());
            inputs.push(sender_input);

            // Compute the padded inputs to keep the RNG in sync.
            for _ in 0..Testnet2::NUM_INPUT_RECORDS - 1 {
                let input = Input::<Testnet2>::new_noop(rng).unwrap();
                serial_numbers.push(input.serial_number().clone());
                inputs.push(input);
            }

            // Generate the expected sender output record
            let sender_output_record = Record::new_output(
                Testnet2::noop_program().program_id(),
                sender.address,
                false,
                100,
                Payload::default(),
                serial_numbers[0].clone(),
                rng,
            )
            .unwrap();

            // Generate the expected recipient output record
            let recipient_output_record = Record::new_output(
                Testnet2::noop_program().program_id(),
                recipient.address,
                false,
                123256,
                Payload::default(),
                serial_numbers[1].clone(),
                rng,
            )
            .unwrap();

            (recipient, sender_output_record, recipient_output_record, serial_numbers)
        };

        // Generate the candidate state transition.
        let (candidate_recipient, candidate_state, candidate_serial_numbers) = {
            let rng = &mut ChaChaRng::seed_from_u64(seed);
            let recipient = Account::new(rng).unwrap();

            let state = StateTransition::new_transfer(
                sender.private_key(),
                &vec![coinbase_record],
                recipient.address,
                AleoAmount::from_bytes(123256),
                AleoAmount::from_bytes(100),
                rng,
            )
            .unwrap();
            let serial_numbers = state.kernel().serial_numbers().clone();

            (recipient, state, serial_numbers)
        };

        assert_eq!(expected_recipient.address, candidate_recipient.address);
        assert_eq!(expected_serial_numbers, candidate_serial_numbers);
        assert_eq!(expected_sender_record, candidate_state.output_records()[0].clone());
        assert_eq!(expected_recipient_record, candidate_state.output_records()[1].clone());
    }
}
