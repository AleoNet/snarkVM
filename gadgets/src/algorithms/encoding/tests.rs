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

mod field_encoding_gadget {
    use crate::{
        algorithms::encoding::{FieldEncodedDataGadget, FieldEncodingGadget},
        AllocGadget,
        EncodingGadget,
        UInt8,
    };
    use snarkvm_algorithms::{encoding::FieldEncodingScheme, EncodingScheme};
    use snarkvm_curves::edwards_bw6::Fr;
    use snarkvm_r1cs::{ConstraintSystem, TestConstraintChecker};

    type TestEncodingScheme = FieldEncodingScheme<Fr>;
    type TestEncodingGadget = FieldEncodingGadget<Fr>;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_encode_equivalence() {
        let mut cs = TestConstraintChecker::<Fr>::new();

        for i in 0..ITERATIONS {
            let data: Vec<u8> = (0..(32 * i)).map(|_| rand::random::<u8>()).collect();
            let encoded_data = TestEncodingScheme::encode(&data).unwrap();

            let data_gadget = UInt8::alloc_vec(cs.ns(|| "allocate data"), &data).unwrap();
            let encoder_data_gadget =
                FieldEncodedDataGadget::<Fr>::alloc(cs.ns(|| "allocate encoded data"), || Ok(encoded_data)).unwrap();

            TestEncodingGadget::enforce_encoding_correctness(
                cs.ns(|| "enforce consistency"),
                &data_gadget,
                &encoder_data_gadget,
            )
            .unwrap();

            if !cs.is_satisfied() {
                println!("{:?}", cs.which_is_unsatisfied());
                assert!(cs.is_satisfied());
            }
        }
    }
}
