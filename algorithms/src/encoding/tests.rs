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

mod field_encoding_scheme {
    use crate::{
        encoding::{FieldEncodedData, FieldEncodingScheme},
        EncodingScheme,
    };
    // `edwards_bw6` is able to touch the corner cases.
    use snarkvm_curves::edwards_bw6::Fr;
    use snarkvm_utilities::{FromBytes, ToBytes};

    const ITERATIONS: usize = 100;

    #[test]
    fn test_encode_and_decode() {
        for i in 0..ITERATIONS {
            let data: Vec<u8> = (0..(32 * i)).map(|_| rand::random::<u8>()).collect();
            let encoded_data = FieldEncodingScheme::<Fr>::encode(&data).unwrap();
            let decoded_data = FieldEncodingScheme::decode(&encoded_data).unwrap();
            assert_eq!(data, decoded_data);
        }
    }

    #[test]
    fn test_to_bytes_le() {
        for i in 0..ITERATIONS {
            let data: Vec<u8> = (0..(32 * i)).map(|_| rand::random::<u8>()).collect();

            let encoded_data = FieldEncodingScheme::encode(&data).unwrap();
            let encoded_data_bytes = encoded_data.to_bytes_le().unwrap();
            let decoded_data = FieldEncodedData::<Fr>::from_bytes_le(&encoded_data_bytes).unwrap();
            assert_eq!(encoded_data, decoded_data);
        }
    }
}
