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
            // println!("{}", message);
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
        debug_assert!(g.is_on_curve());
        debug_assert!(!g.is_in_correct_subgroup_assuming_on_curve());

        let g = g.mul_by_cofactor();
        debug_assert!(g.is_on_curve());
        debug_assert!(g.is_in_correct_subgroup_assuming_on_curve());

        match !g.is_zero() {
            true => return Some(g),
            false => None,
        }
    })
}
