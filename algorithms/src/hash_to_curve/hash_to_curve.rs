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

const ZERO_OFFSET: u32 = 0;
const ONE_OFFSET: u32 = 1;
const TWO_OFFSET: u32 = 2;
const THREE_OFFSET: u32 = 3;

#[inline]
pub fn try_hash_to_curve<G: AffineCurve, const FIELD_BITS: u32, const XOF_DIGEST_LENGTH: u16>(
    input: &str,
) -> Option<(G, u32)> {
    // Try incrementing counter `k` FIELD_BITS times.
    for k in 0..FIELD_BITS {
        // Construct a new message.
        let message = format!("{} in {}", input, k);

        // Output the generator if a valid generator was found.
        if let Some(g) = hash_to_curve::<G, FIELD_BITS, XOF_DIGEST_LENGTH>(&message) {
            println!("{}", message);
            return Some((g, k));
        }
    }
    None
}

#[inline]
pub fn hash_to_curve<G: AffineCurve, const FIELD_BITS: u32, const XOF_DIGEST_LENGTH: u16>(input: &str) -> Option<G> {
    // The number of Blake2Xs invocations needed.
    let num_rounds: u16 = match FIELD_BITS % 256 > 0 {
        true => ((FIELD_BITS / 256) + 1) as u16,
        false => (FIELD_BITS / 256) as u16,
    };

    // Compute the digest for deriving the generator.
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

    // Attempt to use the digest to derive a generator.
    G::from_random_bytes(&digest).and_then(|g| {
        let g = g.mul_by_cofactor();
        match !g.is_zero() {
            true => return Some(g),
            false => None,
        }
    })
}

#[cfg(test)]
mod bls12_377 {
    use crate::hash_to_curve::{hash_to_curve, try_hash_to_curve};
    use snarkvm_curves::{
        bls12_377::{FqParameters, G1Affine, G2Affine},
        AffineCurve,
    };
    use snarkvm_fields::FieldParameters;

    const FIELD_BITS: u32 = FqParameters::MODULUS_BITS;

    #[test]
    fn hash_bls12_377_g1() {
        let g1 = hash_to_curve::<G1Affine, FIELD_BITS, 512>("Aleo BLS12-377 G1 in 2").unwrap();
        assert!(g1.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(g1.x.to_string(), "74043643737953954445837721217321957512753691120262361950112069307233172627234232635736694518632774586903449475895");
        assert_eq!(g1.y.to_string(), "475890735614386331806216012673415025616764851651524824695139553413441593942813660858704892862335035842553512392929");
        assert_eq!(
            try_hash_to_curve::<G1Affine, FIELD_BITS, 512>("Aleo BLS12-377 G1"),
            Some((g1, 2))
        );
    }

    #[test]
    fn hash_bls12_377_g2() {
        let g2 = hash_to_curve::<G2Affine, FIELD_BITS, 512>("Aleo BLS12-377 G2 in 0").unwrap();
        assert!(g2.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(g2.x.to_string(), "Fp2(8675600355291825360916463635111231415651789139955390703452322943018503867687929509188013348679329452611231846015 + 1166248842816419241824176798849550044456714240547651739356426446564995130716104060203219724072241376524554983280488 * u)");
        assert_eq!(g2.y.to_string(), "Fp2(76035893883463787900282266749317306769880679455880335791588090059205303649427288445938168559678721605417431851631 + 11360544497382845311183621525270212659156002841124120676921470451753823629421114580867116244525662375843859815909437 * u)");
        assert_eq!(
            try_hash_to_curve::<G2Affine, FIELD_BITS, 512>("Aleo BLS12-377 G2"),
            Some((g2, 0))
        );
    }
}

#[cfg(test)]
mod bw6_761 {
    use crate::hash_to_curve::{hash_to_curve, try_hash_to_curve};
    use snarkvm_curves::{
        bw6_761::{FqParameters, G1Affine, G2Affine},
        AffineCurve,
    };
    use snarkvm_fields::FieldParameters;

    const FIELD_BITS: u32 = FqParameters::MODULUS_BITS;

    #[test]
    fn hash_bw6_761_g1() {
        let g1 = hash_to_curve::<G1Affine, FIELD_BITS, 768>("Aleo BW6-761 G1 in 6").unwrap();
        assert!(g1.is_in_correct_subgroup_assuming_on_curve());
        // assert_eq!(g1.x.to_string(), "");
        // assert_eq!(g1.y.to_string(), "");
        assert_eq!(
            try_hash_to_curve::<G1Affine, FIELD_BITS, 768>("Aleo BW6-761 G1"),
            Some((g1, 6))
        );
    }

    #[test]
    fn hash_bw6_761_g2() {
        let g2 = hash_to_curve::<G2Affine, FIELD_BITS, 768>("Aleo BW6-761 G2 in 2").unwrap();
        assert!(g2.is_in_correct_subgroup_assuming_on_curve());
        // assert_eq!(g2.x.to_string(), "");
        // assert_eq!(g2.y.to_string(), "");
        assert_eq!(
            try_hash_to_curve::<G2Affine, FIELD_BITS, 768>("Aleo BW6-761 G2"),
            Some((g2, 2))
        );
    }
}
