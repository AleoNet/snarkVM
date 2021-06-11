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

use snarkvm_curves::traits::AffineCurve;
use snarkvm_fields::{FieldParameters, PrimeField, Zero};

#[cfg(feature = "parallel")]
use rayon::prelude::*;
use snarkvm_utilities::BigInteger;

pub fn msm_standard<G: AffineCurve>(
    bases: &[G],
    scalars: &[<G::ScalarField as PrimeField>::BigInteger],
) -> G::Projective {
    use snarkvm_curves::traits::ProjectiveCurve;
    use snarkvm_fields::One;

    let c = if scalars.len() < 32 {
        3
    } else {
        (2.0 / 3.0 * (f64::from(scalars.len() as u32)).log2() + 2.0).ceil() as usize
    };

    let num_bits = <G::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize;
    let fr_one = G::ScalarField::one().into_repr();

    let zero = G::zero().into_projective();
    let window_starts: Vec<_> = (0..num_bits).step_by(c).collect();

    // Each window is of size `c`.
    // We divide up the bits 0..num_bits into windows of size `c`, and
    // in parallel process each such window.
    // window_starts.into_iter() //
    let window_sums: Vec<_> = cfg_into_iter!(window_starts)
        .map(|w_start| {
            let mut res = zero;
            // We don't need the "zero" bucket, so we only have 2^c - 1 buckets
            let mut buckets = vec![zero; (1 << c) - 1];
            scalars
                .iter()
                .zip(bases)
                .filter(|(s, _)| !s.is_zero())
                .for_each(|(&scalar, base)| {
                    if scalar == fr_one {
                        // We only process unit scalars once in the first window.
                        if w_start == 0 {
                            res.add_assign_mixed(base);
                        }
                    } else {
                        let mut scalar = scalar;

                        // We right-shift by w_start, thus getting rid of the
                        // lower bits.
                        scalar.divn(w_start as u32);

                        // We mod the remaining bits by the window size.
                        let scalar = scalar.as_ref()[0] % (1 << c);

                        // If the scalar is non-zero, we update the corresponding
                        // bucket.
                        // (Recall that `buckets` doesn't have a zero bucket.)
                        if scalar != 0 {
                            buckets[(scalar - 1) as usize].add_assign_mixed(&base);
                        }
                    }
                });
            G::Projective::batch_normalization(&mut buckets);

            let mut running_sum = G::Projective::zero();
            for b in buckets.into_iter().map(|g| g.into_affine()).rev() {
                running_sum.add_assign_mixed(&b);
                res += &running_sum;
            }

            res
        })
        .collect();

    // We store the sum for the lowest window.
    let lowest = window_sums.first().unwrap();

    // We're traversing windows from high to low.
    window_sums[1..].iter().rev().fold(zero, |mut total, sum_i| {
        total += sum_i;
        for _ in 0..c {
            total.double_in_place();
        }
        total
    }) + lowest
}
