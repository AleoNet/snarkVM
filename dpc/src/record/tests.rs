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

use crate::{record::*, testnet2::*, Account, AccountScheme, Network, Payload, Record, ViewKey, PAYLOAD_SIZE};
use snarkvm_utilities::{FromBytes, UniformRand};

use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

pub(crate) const ITERATIONS: usize = 25;

#[test]
fn test_record_ciphertext() {
    let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        let account = Account::<Testnet2>::new(rng);

        let value = rng.gen();
        let mut payload = [0u8; PAYLOAD_SIZE];
        rng.fill(&mut payload);

        let expected_record = Record::new_input(
            account.address(),
            value,
            Payload::from_bytes_le(&payload).unwrap(),
            *Testnet2::noop_program_id(),
            UniformRand::rand(rng),
            UniformRand::rand(rng),
        )
        .unwrap();

        // Encrypt the record.
        let (record_ciphertext, _) = RecordCiphertext::encrypt(&expected_record, rng).unwrap();

        // Decrypt the record.
        let account_view_key = ViewKey::from_private_key(&account.private_key());
        let candidate_record = record_ciphertext.decrypt(&account_view_key).unwrap();
        assert_eq!(expected_record, candidate_record);
    }
}
