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

use super::{Affine, Projective};
use crate::{AffineCurve, ProjectiveCurve, ShortWeierstrassParameters};
use snarkvm_fields::Zero;
use snarkvm_utilities::{
    io::Cursor,
    rand::Uniform,
    serialize::{CanonicalDeserialize, CanonicalSerialize},
    Compress,
    Validate,
};

use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

pub const ITERATIONS: usize = 10;

pub fn sw_tests<P: ShortWeierstrassParameters>() {
    sw_curve_serialization_test::<P>();
    sw_from_random_bytes::<P>();
}

pub fn sw_curve_serialization_test<P: ShortWeierstrassParameters>() {
    let modes = [
        (Compress::Yes, Validate::Yes),
        (Compress::No, Validate::No),
        (Compress::Yes, Validate::No),
        (Compress::No, Validate::Yes),
    ];
    for (compress, validate) in modes {
        let buf_size = Affine::<P>::zero().serialized_size(compress);

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        for _ in 0..10 {
            let a = Projective::<P>::rand(&mut rng);
            let mut a = a.to_affine();
            {
                let mut serialized = vec![0; buf_size];
                let mut cursor = Cursor::new(&mut serialized[..]);
                a.serialize_with_mode(&mut cursor, compress).unwrap();

                let mut cursor = Cursor::new(&serialized[..]);
                let b = Affine::<P>::deserialize_with_mode(&mut cursor, compress, validate).unwrap();
                assert_eq!(a, b);
            }

            {
                a.y = -a.y;
                let mut serialized = vec![0; buf_size];
                let mut cursor = Cursor::new(&mut serialized[..]);
                a.serialize_with_mode(&mut cursor, compress).unwrap();
                let mut cursor = Cursor::new(&serialized[..]);
                let b = Affine::<P>::deserialize_with_mode(&mut cursor, compress, validate).unwrap();
                assert_eq!(a, b);
            }

            {
                let a = Affine::<P>::zero();
                let mut serialized = vec![0; buf_size];
                let mut cursor = Cursor::new(&mut serialized[..]);
                a.serialize_with_mode(&mut cursor, compress).unwrap();
                let mut cursor = Cursor::new(&serialized[..]);
                let b = Affine::<P>::deserialize_with_mode(&mut cursor, compress, validate).unwrap();
                assert_eq!(a, b);
            }

            {
                let a = Affine::<P>::zero();
                let mut serialized = vec![0; buf_size - 1];
                let mut cursor = Cursor::new(&mut serialized[..]);
                a.serialize_with_mode(&mut cursor, compress).unwrap_err();
            }

            {
                let serialized = vec![0; buf_size - 1];
                let mut cursor = Cursor::new(&serialized[..]);
                Affine::<P>::deserialize_with_mode(&mut cursor, compress, validate).unwrap_err();
            }

            {
                let mut serialized = vec![0; a.uncompressed_size()];
                let mut cursor = Cursor::new(&mut serialized[..]);
                a.serialize_uncompressed(&mut cursor).unwrap();

                let mut cursor = Cursor::new(&serialized[..]);
                let b = Affine::<P>::deserialize_uncompressed(&mut cursor).unwrap();
                assert_eq!(a, b);
            }

            {
                a.y = -a.y;
                let mut serialized = vec![0; a.uncompressed_size()];
                let mut cursor = Cursor::new(&mut serialized[..]);
                a.serialize_uncompressed(&mut cursor).unwrap();
                let mut cursor = Cursor::new(&serialized[..]);
                let b = Affine::<P>::deserialize_uncompressed(&mut cursor).unwrap();
                assert_eq!(a, b);
            }

            {
                let a = Affine::<P>::zero();
                let mut serialized = vec![0; a.uncompressed_size()];
                let mut cursor = Cursor::new(&mut serialized[..]);
                a.serialize_uncompressed(&mut cursor).unwrap();
                let mut cursor = Cursor::new(&serialized[..]);
                let b = Affine::<P>::deserialize_uncompressed(&mut cursor).unwrap();
                assert_eq!(a, b);
            }
        }
    }
}

pub fn sw_from_random_bytes<P: ShortWeierstrassParameters>() {
    let buf_size = Affine::<P>::zero().compressed_size();

    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

    for _ in 0..ITERATIONS {
        let a = Projective::<P>::rand(&mut rng);
        let a = a.to_affine();
        {
            let mut serialized = vec![0; buf_size];
            let mut cursor = Cursor::new(&mut serialized[..]);
            a.serialize_compressed(&mut cursor).unwrap();

            let mut cursor = Cursor::new(&serialized[..]);
            let p1 = Affine::<P>::deserialize_compressed(&mut cursor).unwrap();
            let p2 = Affine::<P>::from_random_bytes(&serialized).unwrap();
            assert_eq!(p1, p2);
        }
    }
}
