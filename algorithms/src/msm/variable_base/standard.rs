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

use crate::msm::MSMStrategy;
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

fn standard_window<G: AffineCurve>(
    bases: &[G],
    scalars: &[<G::ScalarField as PrimeField>::BigInteger],
    w_start: usize,
    c: usize,
) -> (G::Projective, usize) {
    let mut res = G::Projective::zero();
    let fr_one = G::ScalarField::one().to_repr();

    // We only process unit scalars once in the first window.
    if w_start == 0 {
        scalars.iter().zip(bases).filter(|(&s, _)| s == fr_one).for_each(|(_, base)| {
            res.add_assign_mixed(base);
        });
    }

    // We don't need the "zero" bucket, so we only have 2^c - 1 buckets
    let window_size = if (w_start % c) != 0 { w_start % c } else { c };
    let mut buckets = vec![G::Projective::zero(); (1 << window_size) - 1];
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

    (res, window_size)
}

fn batched_window<G: AffineCurve>(
    bases: &[G],
    scalars: &[<G::ScalarField as PrimeField>::BigInteger],
    w_start: usize,
    c: usize,
    strategy: MSMStrategy,
) -> (G::Projective, usize) {
    // We don't need the "zero" bucket, so we only have 2^c - 1 buckets
    let window_size = if (w_start % c) != 0 { w_start % c } else { c };
    let num_buckets = (1 << window_size) - 1;

    let mut bucket_positions: Vec<_> = scalars
        .iter()
        .enumerate()
        .map(|(scalar_index, &scalar)| {
            let mut scalar = scalar;

            // We right-shift by w_start, thus getting rid of the lower bits.
            scalar.divn(w_start as u32);

            // We mod the remaining bits by the window size.
            let scalar = (scalar.as_ref()[0] % (1 << c)) as i32;

            BucketPosition { bucket_index: (scalar - 1) as u32, scalar_index: scalar_index as u32 }
        })
        .collect();

    let buckets = match strategy {
        MSMStrategy::BatchedA => batch_add_a::<G>(num_buckets, &bases[..], &mut bucket_positions[..]),
        MSMStrategy::BatchedB => batch_add_b::<G>(num_buckets, &bases[..], &mut bucket_positions[..]),
        _ => panic!("Invalid MSM strategy provided, use either BatchedA or BatchedB"),
    };

    let mut res = G::Projective::zero();
    let mut running_sum = G::Projective::zero();
    for b in buckets.into_iter().rev() {
        running_sum.add_assign_mixed(&b);
        res += &running_sum;
    }

    (res, window_size)
}

pub(super) fn msm<G: AffineCurve>(
    bases: &[G],
    scalars: &[<G::ScalarField as PrimeField>::BigInteger],
    strategy: MSMStrategy,
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
    let window_sums: Vec<_> = cfg_into_iter!(0..num_bits)
        .step_by(c)
        .map(|w_start| match strategy {
            MSMStrategy::Standard => standard_window(bases, scalars, w_start, c),
            _ => batched_window(bases, scalars, w_start, c, strategy),
        })
        .collect();

    // We store the sum for the lowest window.
    let (lowest, window_sums) = window_sums.split_first().unwrap();

    // We're traversing windows from high to low.
    window_sums.iter().rev().fold(G::Projective::zero(), |mut total, (sum_i, window_size)| {
        total += sum_i;
        for _ in 0..*window_size {
            total.double_in_place();
        }
        total
    }) + lowest.0
}

/// We use a batch size that is big enough to amortise the cost of the actual inversion
/// close to zero while not straining the CPU cache by generating and fetching from
/// large w-NAF tables and slices [G]
pub const BATCH_SIZE: usize = 4096;

use core::cmp::Ordering;
use voracious_radix_sort::*;

#[cfg(not(feature = "std"))]
use crate::fft::domain::log2;

#[derive(Copy, Clone, Debug)]
pub struct BucketPosition {
    pub bucket_index: u32,
    pub scalar_index: u32,
}

impl PartialOrd for BucketPosition {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.bucket_index.partial_cmp(&other.bucket_index)
    }
}

impl Radixable<u32> for BucketPosition {
    type Key = u32;

    #[inline]
    fn key(&self) -> Self::Key {
        self.bucket_index
    }
}

impl PartialEq for BucketPosition {
    fn eq(&self, other: &Self) -> bool {
        self.bucket_index == other.bucket_index
    }
}

#[inline]
pub fn batch_add_a<G: AffineCurve>(num_buckets: usize, bases: &[G], bucket_positions: &mut [BucketPosition]) -> Vec<G> {
    // assert_eq!(elems.len(), bucket_positions.len());
    assert!(bases.len() > 0);

    dlsd_radixsort(bucket_positions, 8);

    let mut num_scalars = bucket_positions.len();
    let mut all_ones = true;
    let mut new_len = 0; // len counter
    let mut global_counter = 0; // global counters
    let mut local_counter = 1; // local counter
    let mut batch = 0; // batch counter

    let mut instr = Vec::<(u32, u32)>::with_capacity(BATCH_SIZE);
    let mut new_bases = Vec::<G>::with_capacity(bases.len() * 3 / 8);
    let mut scratch_space = Vec::<Option<G>>::with_capacity(BATCH_SIZE / 2);

    // In the first loop, copy the results of the first in-place addition tree to the vector `new_bases`.
    while global_counter < num_scalars {
        let current_bucket = bucket_positions[global_counter].bucket_index;
        while global_counter + 1 < num_scalars && bucket_positions[global_counter + 1].bucket_index == current_bucket {
            global_counter += 1;
            local_counter += 1;
        }
        if current_bucket >= num_buckets as u32 {
            local_counter = 1;
        } else if local_counter > 1 {
            // all ones is false if next len is not 1
            if local_counter > 2 {
                all_ones = false;
            }
            let is_odd = local_counter % 2 == 1;
            let half = local_counter / 2;
            for i in 0..half {
                instr.push((
                    bucket_positions[global_counter - (local_counter - 1) + 2 * i].scalar_index,
                    bucket_positions[global_counter - (local_counter - 1) + 2 * i + 1].scalar_index,
                ));
                bucket_positions[new_len + i] =
                    BucketPosition { bucket_index: current_bucket, scalar_index: (new_len + i) as u32 };
            }
            if is_odd {
                instr.push((bucket_positions[global_counter].scalar_index, !0u32));
                bucket_positions[new_len + half] =
                    BucketPosition { bucket_index: current_bucket, scalar_index: (new_len + half) as u32 };
            }
            // Reset the local_counter and update state
            new_len += half + (local_counter % 2);
            batch += half;
            local_counter = 1;

            if batch >= BATCH_SIZE / 2 {
                // We need instructions for copying data in the case
                // of noops. We encode noops/copies as !0u32
                G::batch_add_write(&bases[..], &instr[..], &mut new_bases, &mut scratch_space);

                instr.clear();
                batch = 0;
            }
        } else {
            instr.push((bucket_positions[global_counter].scalar_index, !0u32));
            bucket_positions[new_len] = BucketPosition { bucket_index: current_bucket, scalar_index: new_len as u32 };
            new_len += 1;
        }
        global_counter += 1;
    }
    if instr.len() > 0 {
        G::batch_add_write(&bases[..], &instr[..], &mut new_bases, &mut scratch_space);
        instr.clear();
    }
    global_counter = 0;
    batch = 0;
    local_counter = 1;
    num_scalars = new_len;
    new_len = 0;

    // Next, perform all the updates in place.
    while !all_ones {
        all_ones = true;
        while global_counter < num_scalars {
            let current_bucket = bucket_positions[global_counter].bucket_index;
            while global_counter + 1 < num_scalars
                && bucket_positions[global_counter + 1].bucket_index == current_bucket
            {
                global_counter += 1;
                local_counter += 1;
            }
            if current_bucket >= num_buckets as u32 {
                local_counter = 1;
            } else if local_counter > 1 {
                // all ones is false if next len is not 1
                if local_counter != 2 {
                    all_ones = false;
                }
                let is_odd = local_counter % 2 == 1;
                let half = local_counter / 2;
                for i in 0..half {
                    instr.push((
                        bucket_positions[global_counter - (local_counter - 1) + 2 * i].scalar_index,
                        bucket_positions[global_counter - (local_counter - 1) + 2 * i + 1].scalar_index,
                    ));
                    bucket_positions[new_len + i] = bucket_positions[global_counter - (local_counter - 1) + 2 * i];
                }
                if is_odd {
                    bucket_positions[new_len + half] = bucket_positions[global_counter];
                }
                // Reset the local_counter and update state
                new_len += half + (local_counter % 2);
                batch += half;
                local_counter = 1;

                if batch >= BATCH_SIZE / 2 {
                    G::batch_add_in_place_same_slice(&mut new_bases[..], &instr[..]);
                    instr.clear();
                    batch = 0;
                }
            } else {
                bucket_positions[new_len] = bucket_positions[global_counter];
                new_len += 1;
            }
            global_counter += 1;
        }
        if instr.len() > 0 {
            G::batch_add_in_place_same_slice(&mut new_bases[..], &instr[..]);
            instr.clear();
        }
        global_counter = 0;
        batch = 0;
        local_counter = 1;
        num_scalars = new_len;
        new_len = 0;
    }

    let mut res = vec![G::zero(); num_buckets];
    for i in 0..num_scalars {
        let (pos, buc) = (bucket_positions[i].scalar_index, bucket_positions[i].bucket_index);
        res[buc as usize] = new_bases[pos as usize];
    }
    res
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

pub fn batch_add_b<G: AffineCurve>(buckets: usize, bases: &[G], bucket_assign: &[BucketPosition]) -> Vec<G> {
    let mut bases = bases.to_vec();
    let num_split = 2i32.pow(log2(buckets) / 2 + 2) as usize;
    let split_size = (buckets - 1) / num_split + 1;
    let ratio = bases.len() / buckets * 2;

    // Get the inverted index for the positions assigning to each bucket
    let mut bucket_split = vec![vec![]; num_split];
    let mut index = vec![Vec::with_capacity(ratio); buckets];

    for bucket_pos in bucket_assign.iter() {
        let (bucket_index, scalar_index) = (bucket_pos.bucket_index as usize, bucket_pos.scalar_index as usize);
        // Check the bucket assignment is valid
        if bucket_index < buckets {
            // index[bucket].push(position);
            bucket_split[bucket_index / split_size].push((bucket_index, scalar_index));
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
            G::batch_add_in_place_same_slice(&mut bases[..], &instr[..]);
        }
    }

    let mut res = vec![G::zero(); buckets];

    for (i, to_add) in index.iter().enumerate() {
        if to_add.len() == 1 {
            res[i] = bases[to_add[0] as usize];
        } else if to_add.len() > 1 {
            debug_assert!(false, "Did not successfully reduce to_add");
        }
    }
    res
}
