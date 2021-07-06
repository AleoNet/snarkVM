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

use crate::prf::{Blake2Xs, ALEO_PERSONA};
use snarkvm_curves::AffineCurve;
use snarkvm_fields::Field;
use snarkvm_utilities::{bits_to_bytes, bytes_to_bits};

const ZERO_OFFSET: u32 = 0;
const ONE_OFFSET: u32 = 1;
const TWO_OFFSET: u32 = 2;
const THREE_OFFSET: u32 = 3;

pub fn hash_to_curve<G: AffineCurve<BaseField = F>, F: Field, const FIELD_BITS: u32, const XOF_DIGEST_LENGTH: u16>(
    input: &str,
) -> Option<G> {
    // The number of Blake2Xs invocations needed.
    let num_rounds: u16 = match FIELD_BITS % 256 > 0 {
        true => ((FIELD_BITS / 256) + 1) as u16,
        false => (FIELD_BITS / 256) as u16,
    };

    let mut digest = Vec::with_capacity(XOF_DIGEST_LENGTH as usize);
    for offset in 0..=num_rounds {
        digest.extend_from_slice(&match offset {
            0 => Blake2Xs::evaluate::<ZERO_OFFSET, XOF_DIGEST_LENGTH, ALEO_PERSONA>(input.as_bytes()),
            1 => Blake2Xs::evaluate::<ONE_OFFSET, XOF_DIGEST_LENGTH, ALEO_PERSONA>(input.as_bytes()),
            2 => Blake2Xs::evaluate::<TWO_OFFSET, XOF_DIGEST_LENGTH, ALEO_PERSONA>(input.as_bytes()),
            3 => Blake2Xs::evaluate::<THREE_OFFSET, XOF_DIGEST_LENGTH, ALEO_PERSONA>(input.as_bytes()),
            _ => unimplemented!("hash_to_curve supports up to a 1024-bit base field element"),
        });
    }

    let mut x_bits: Vec<bool> = bytes_to_bits(&digest).take((FIELD_BITS + 1) as usize).collect(); // TODO (howardwu): Add le/be ending to method.
    println!("{}", x_bits.len());
    let y_sign = x_bits.pop().unwrap();

    match G::BaseField::from_random_bytes(&bits_to_bytes(&x_bits)) {
        Some(x) => match G::from_x_coordinate(x, y_sign) {
            Some(g) => {
                let g = g.mul_by_cofactor();
                match !g.is_zero() {
                    true => return Some(g),
                    false => None,
                }
            }
            None => None,
        },
        None => None,
    }
}

#[cfg(test)]
mod bls12_377 {
    use crate::hash_to_curve::hash_to_curve;
    use snarkvm_curves::{
        bls12_377::{Fq, Fq2Parameters, G1Affine, G2Affine},
        AffineCurve,
    };
    use snarkvm_fields::{FieldParameters, Fp2, PrimeField};

    const FIELD_BITS: u32 = <Fq as PrimeField>::Parameters::MODULUS_BITS;

    #[test]
    fn hash_bls12_377_g1() {
        let g1 = hash_to_curve::<G1Affine, Fq, FIELD_BITS, 512>("Aleo BLS12-377 G1").unwrap();
        assert!(g1.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(g1.x.to_string(), "TBD");
        assert_eq!(g1.y.to_string(), "TBD");
    }

    #[test]
    fn hash_bls12_377_g2() {
        let g2 = hash_to_curve::<G2Affine, Fp2<Fq2Parameters>, FIELD_BITS, 512>("Aleo BLS12-377 G2").unwrap();
        assert!(g2.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(g2.x.to_string(), "TBD");
        assert_eq!(g2.y.to_string(), "TBD");
    }
}
