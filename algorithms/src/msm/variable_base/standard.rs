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

use snarkvm_curves::{traits::AffineCurve, Group, ProjectiveCurve};
use snarkvm_fields::{One, PrimeField, Zero};
use snarkvm_utilities::{cfg_into_iter, BigInteger};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

fn update_buckets<G: AffineCurve>(
    base: &G,
    mut scalar: <G::ScalarField as PrimeField>::BigInteger,
    w_start: usize,
    c: usize,
    buckets: &mut [G::Projective],
) {
    // We right-shift by w_start, thus getting rid of the lower bits.
    scalar.divn(w_start as u32);

    // We mod the remaining bits by the window size.
    let scalar = scalar.as_ref()[0] % (1 << c);

    // If the scalar is non-zero, we update the corresponding bucket.
    // (Recall that `buckets` doesn't have a zero bucket.)
    if scalar != 0 {
        buckets[(scalar - 1) as usize].add_assign_mixed(base);
    }
}

fn process_window<G: AffineCurve>(
    bases: &[G],
    scalars: &[<G::ScalarField as PrimeField>::BigInteger],
    w_start: usize,
    c: usize,
) -> G::Projective {
    let mut res = G::Projective::zero();
    let fr_one = G::ScalarField::one().to_repr();

    // We only process unit scalars once in the first window.
    if w_start == 0 {
        scalars.iter().zip(bases).filter(|(&s, _)| s == fr_one).for_each(|(_, base)| {
            res.add_assign_mixed(base);
        });
    }

    // We don't need the "zero" bucket, so we only have 2^c - 1 buckets
    let mut buckets = vec![G::Projective::zero(); (1 << c) - 1];
    scalars
        .iter()
        .zip(bases)
        .filter(|(&s, _)| s > fr_one)
        .for_each(|(&scalar, base)| update_buckets(base, scalar, w_start, c, &mut buckets));
    // G::Projective::batch_normalization(&mut buckets);

    for running_sum in buckets.into_iter().rev().scan(G::Projective::zero(), |sum, b| {
        *sum += b;
        Some(*sum)
    }) {
        res += running_sum;
    }

    res
}

pub(super) fn msm_standard<G: AffineCurve>(
    bases: &[G],
    scalars: &[<G::ScalarField as PrimeField>::BigInteger],
) -> G::Projective {
    // Determine the bucket size `c` (chosen empirically).
    let c = match scalars.len() < 32 {
        true => 3,
        false => crate::msm::ln_without_floats(scalars.len()) + 2,
    };

    let num_bits = <G::ScalarField as PrimeField>::size_in_bits();

    // Each window is of size `c`.
    // We divide up the bits 0..num_bits into windows of size `c`, and
    // in parallel process each such window.
    let window_sums: Vec<_> =
        cfg_into_iter!(0..num_bits).step_by(c).map(|w_start| process_window(bases, scalars, w_start, c)).collect();

    // We store the sum for the lowest window.
    let (lowest, window_sums) = window_sums.split_first().unwrap();

    // We're traversing windows from high to low.
    window_sums.iter().rev().fold(G::Projective::zero(), |mut total, sum_i| {
        total += sum_i;
        for _ in 0..c {
            total.double_in_place();
        }
        total
    }) + lowest
}

pub(super) fn msm_standard_batched<G: AffineCurve>(
    bases: &[G],
    scalars: &[<G::ScalarField as PrimeField>::BigInteger],
) -> G::Projective {
    let c = match scalars.len() < 32 {
        true => 3,
        false => crate::msm::ln_without_floats(scalars.len()) + 2,
    };

    let num_bits = <G::ScalarField as PrimeField>::size_in_bits();
    let zero = G::Projective::zero();

    // Each window is of size `c`.
    // We divide up the bits 0..num_bits into windows of size `c`, and
    // in parallel process each such window.
    let window_sums: Vec<_> = cfg_into_iter!(0..num_bits)
        .step_by(c)
        .map(|w_start| {
            // We don't need the "zero" bucket, so we only have 2^c - 1 buckets
            let log2_n_bucket = if (w_start % c) != 0 { w_start % c } else { c };
            let n_buckets = (1 << log2_n_bucket) - 1;

            let mut bucket_positions: Vec<_> = scalars
                .iter()
                .enumerate()
                .map(|(pos, &scalar)| {
                    let mut scalar = scalar;

                    // We right-shift by w_start, thus getting rid of the
                    // lower bits.
                    scalar.divn(w_start as u32);

                    // We mod the remaining bits by the window size.
                    let res = (scalar.as_ref()[0] % (1 << c)) as i32;
                    BucketPosition { bucket: (res - 1) as u32, position: pos as u32 }
                })
                .collect();

            let buckets = batch_add_bucket::<G>(n_buckets, &bases[..], &mut bucket_positions[..]);

            let mut res = zero;
            let mut running_sum = G::Projective::zero();
            for b in buckets.into_iter().rev() {
                running_sum.add_assign_mixed(&b);
                res += &running_sum;
            }

            (res, log2_n_bucket)
        })
        .collect();

    // We store the sum for the lowest window.
    let lowest = window_sums.first().unwrap().0;

    // We're traversing windows from high to low.
    lowest
        + &window_sums[1..].iter().rev().fold(
            zero,
            |total: G::Projective, (sum_i, window_size): &(G::Projective, usize)| {
                let mut total = total + sum_i;
                for _ in 0..*window_size {
                    total.double_in_place();
                }
                total
            },
        )
}

/// We use a batch size that is big enough to amortise the cost of the actual inversion
/// close to zero while not straining the CPU cache by generating and fetching from
/// large w-NAF tables and slices [G]
pub const BATCH_SIZE: usize = 4096;

use core::cmp::Ordering;

#[cfg(not(feature = "std"))]
use crate::fft::domain::log2;

#[derive(Copy, Clone, Debug)]
pub struct BucketPosition {
    pub bucket: u32,
    pub position: u32,
}

impl PartialOrd for BucketPosition {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.bucket.partial_cmp(&other.bucket)
    }
}

impl PartialEq for BucketPosition {
    fn eq(&self, other: &Self) -> bool {
        self.bucket == other.bucket
    }
}

/// Chunks vectorised instructions into a size that does not require
/// storing a lot of intermediate state
fn get_chunked_instr<T: Clone>(instr: &[T], batch_size: usize) -> Vec<Vec<T>> {
    let mut res = Vec::new();

    let rem = instr.chunks_exact(batch_size).remainder();
    let mut chunks = instr.chunks_exact(batch_size).peekable();

    if chunks.len() == 0 {
        res.push(rem.to_vec());
    }

    while let Some(chunk) = chunks.next() {
        let chunk = if chunks.peek().is_none() { [chunk, rem].concat() } else { chunk.to_vec() };
        res.push(chunk);
    }
    res
}

pub fn batch_add_bucket<C: AffineCurve>(buckets: usize, elems: &[C], bucket_assign: &[BucketPosition]) -> Vec<C> {
    let mut elems = elems.to_vec();
    let num_split = 2i32.pow(log2(buckets) / 2 + 2) as usize;
    let split_size = (buckets - 1) / num_split + 1;
    let ratio = elems.len() / buckets * 2;
    // Get the inverted index for the positions assigning to each bucket
    let mut bucket_split = vec![vec![]; num_split];
    let mut index = vec![Vec::with_capacity(ratio); buckets];

    for bucket_pos in bucket_assign.iter() {
        let (bucket, position) = (bucket_pos.bucket as usize, bucket_pos.position as usize);
        // Check the bucket assignment is valid
        if bucket < buckets {
            // index[bucket].push(position);
            bucket_split[bucket / split_size].push((bucket, position));
        }
    }

    for split in bucket_split {
        for (bucket, position) in split {
            index[bucket].push(position as u32);
        }
    }

    // Instructions for indexes for the in place addition tree
    let mut instr: Vec<Vec<(u32, u32)>> = vec![];
    // Find the maximum depth of the addition tree
    let max_depth = index.iter()
        // log_2
        .map(|x| log2(x.len()))
        .max().unwrap();

    // Generate in-place addition instructions that implement the addition tree
    // for each bucket from the leaves to the root
    for i in 0..max_depth {
        let mut instr_row = Vec::<(u32, u32)>::with_capacity(buckets);
        for to_add in index.iter_mut() {
            if to_add.len() > 1 << (max_depth - i - 1) {
                let mut new_to_add = vec![];
                for j in 0..(to_add.len() / 2) {
                    new_to_add.push(to_add[2 * j]);
                    instr_row.push((to_add[2 * j], to_add[2 * j + 1]));
                }
                if to_add.len() % 2 == 1 {
                    new_to_add.push(*to_add.last().unwrap());
                }
                *to_add = new_to_add;
            }
        }
        instr.push(instr_row);
    }

    for instr_row in instr.iter() {
        for instr in get_chunked_instr::<(u32, u32)>(&instr_row[..], BATCH_SIZE).iter() {
            C::batch_add_in_place_same_slice(&mut elems[..], &instr[..]);
        }
    }

    let mut res = vec![C::zero(); buckets];

    for (i, to_add) in index.iter().enumerate() {
        if to_add.len() == 1 {
            res[i] = elems[to_add[0] as usize];
        } else if to_add.len() > 1 {
            debug_assert!(false, "Did not successfully reduce to_add");
        }
    }
    res
}
