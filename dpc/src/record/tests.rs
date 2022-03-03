// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::{testnet2::*, Account, AleoAmount, Network, Payload, Record, ViewKey};
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::{Rng, SeedableRng};
use rand_chacha::ChaChaRng;

pub(crate) const ITERATIONS: usize = 25;

#[test]
fn test_record_ciphertext() {
    let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        let account = Account::<Testnet2>::new(rng);

        let value: i64 = rng.gen();
        let mut payload = [0u8; Testnet2::RECORD_PAYLOAD_SIZE_IN_BYTES];
        rng.fill(&mut payload);

        let expected_record = Record::new(
            account.address(),
            AleoAmount::from_gate(value),
            Some(Payload::from_bytes_le(&payload).unwrap()),
            None,
            rng,
        )
        .unwrap();

        // Encrypt the record.
        let record_ciphertext = expected_record.ciphertext();
        // TODO (raychu86): Make sure the program id size is included.
        assert_eq!(Testnet2::RECORD_CIPHERTEXT_SIZE_IN_BYTES, (*record_ciphertext).to_bytes_le().unwrap().len());

        // Decrypt the record.
        let account_view_key = ViewKey::from_private_key(account.private_key());
        let candidate_record = Record::decrypt(&account_view_key.into(), record_ciphertext).unwrap();
        assert_eq!(expected_record, candidate_record);
    }
}
