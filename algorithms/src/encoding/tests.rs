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

mod packed_fields_and_bytes {
    use rand::SeedableRng;
    use rand_chacha::ChaChaRng;
    use snarkvm_curves::edwards_bw6::Fr;
    // edwards_bw6 is able to touch the corner cases.
    use crate::{
        encoding::{FieldEncodedData, FieldEncodingScheme},
        EncodingScheme,
    };
    use snarkvm_utilities::{FromBytes, ToBytes, UniformRand};

    #[test]
    fn correctness_test() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        for test_len in 0..100 {
            let mut bytes = Vec::with_capacity(test_len);
            for _ in 0..test_len {
                bytes.push(u8::rand(&mut rng));
            }

            let encoder = FieldEncodingScheme::<Fr>::default();
            let encoded_data = encoder.encode(&bytes).unwrap();

            let decoded_result = encoder.decode(&encoded_data).unwrap();

            assert_eq!(bytes, decoded_result);
        }
    }

    #[test]
    fn serialization_test() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        for test_len in 0..50 {
            let mut bytes = Vec::with_capacity(test_len);
            for _ in 0..test_len {
                bytes.push(u8::rand(&mut rng));
            }

            let encoder = FieldEncodingScheme::<Fr>::default();
            let encoded_record = encoder.encode(&bytes).unwrap();

            let serialized_encoded_record = encoded_record.to_bytes_le().unwrap();
            let deserialized_encoded_record =
                FieldEncodedData::<Fr>::from_bytes_le(&serialized_encoded_record).unwrap();

            assert_eq!(encoded_record, deserialized_encoded_record);
        }
    }
}
