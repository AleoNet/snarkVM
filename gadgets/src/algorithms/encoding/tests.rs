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
    use crate::{
        algorithms::encoding::{PackedFieldsAndBytesEncodingGadget, PackedFieldsAndBytesGadget},
        AllocGadget,
        EncodingGadget,
        UInt8,
    };
    use rand::SeedableRng;
    use rand_chacha::ChaChaRng;
    use snarkvm_algorithms::{encoding::PackedFieldsAndBytesEncodingScheme, EncodingScheme};
    use snarkvm_curves::edwards_bw6::Fr;
    use snarkvm_r1cs::{ConstraintSystem, TestConstraintChecker};
    use snarkvm_utilities::UniformRand;

    type TestEncodingScheme = PackedFieldsAndBytesEncodingScheme<Fr>;
    type TestEncodingGadget = PackedFieldsAndBytesEncodingGadget<Fr>;

    #[test]
    fn test_consistency() {
        let mut cs = TestConstraintChecker::<Fr>::new();
        let mut rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

        let encoding_scheme = TestEncodingScheme::setup("test_encoding_gadget");
        let encoding_gadget = TestEncodingGadget::alloc_constant(&mut cs.ns(|| "allocate encoding gadget"), || {
            Ok(encoding_scheme.clone())
        })
        .unwrap();

        for test_len in 0..100 {
            let mut bytes = Vec::with_capacity(test_len);
            for _ in 0..test_len {
                bytes.push(u8::rand(&mut rng));
            }

            let encoded_data = encoding_scheme.encode(&bytes).unwrap();

            let data_gadget = UInt8::alloc_vec(cs.ns(|| "allocate data"), &bytes).unwrap();
            let encoder_data_gadget =
                PackedFieldsAndBytesGadget::<Fr>::alloc(cs.ns(|| "allocate encoded data"), || Ok(encoded_data))
                    .unwrap();

            encoding_gadget
                .enforce_encoding_correctness(cs.ns(|| "enforce consistency"), &data_gadget, &encoder_data_gadget)
                .unwrap();

            if !cs.is_satisfied() {
                println!("{:?}", cs.which_is_unsatisfied());
                assert!(cs.is_satisfied());
            }
        }
    }
}
