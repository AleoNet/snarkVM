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
use snarkvm_fields::{PrimeField, Zero};
use snarkvm_utilities::{cfg_into_iter, BigInteger};

use core::cmp::Ordering;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// We use a batch size that is big enough to amortise the cost of the actual inversion
/// close to zero while not straining the CPU cache by generating and fetching from
/// large w-NAF tables and slices [G]
pub const BATCH_SIZE: usize = 300;

#[derive(Copy, Clone, Debug)]
pub struct BucketPosition {
    pub bucket_index: u32,
    pub scalar_index: u32,
}

impl Eq for BucketPosition {}

impl PartialEq for BucketPosition {
    fn eq(&self, other: &Self) -> bool {
        self.bucket_index == other.bucket_index
    }
}

impl Ord for BucketPosition {
    fn cmp(&self, other: &Self) -> Ordering {
        self.bucket_index.cmp(&other.bucket_index)
    }
}

impl PartialOrd for BucketPosition {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.bucket_index.partial_cmp(&other.bucket_index)
    }
}

#[inline]
pub fn batch_add<G: AffineCurve>(num_buckets: usize, bases: &[G], bucket_positions: &mut [BucketPosition]) -> Vec<G> {
    // assert_eq!(elems.len(), bucket_positions.len());
    assert!(!bases.is_empty());

    bucket_positions.sort_unstable();

    let mut num_scalars = bucket_positions.len();
    let mut all_ones = true;
    let mut new_len = 0; // len counter
    let mut global_counter = 0; // global counters
    let mut local_counter = 1; // local counter
    let mut number_of_bases_in_batch = 0;

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
            number_of_bases_in_batch += half;
            local_counter = 1;

            // When the number of bases in a batch crosses the threshold, perform a batch addition.
            if number_of_bases_in_batch >= BATCH_SIZE / 2 {
                // We need instructions for copying data in the case of noops.
                // We encode noops/copies as !0u32
                G::batch_add_write(bases, &instr, &mut new_bases, &mut scratch_space);

                instr.clear();
                number_of_bases_in_batch = 0;
            }
        } else {
            instr.push((bucket_positions[global_counter].scalar_index, !0u32));
            bucket_positions[new_len] = BucketPosition { bucket_index: current_bucket, scalar_index: new_len as u32 };
            new_len += 1;
        }
        global_counter += 1;
    }
    if !instr.is_empty() {
        G::batch_add_write(bases, &instr, &mut new_bases, &mut scratch_space);
        instr.clear();
    }
    global_counter = 0;
    number_of_bases_in_batch = 0;
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
                number_of_bases_in_batch += half;
                local_counter = 1;

                if number_of_bases_in_batch >= BATCH_SIZE / 2 {
                    G::batch_add_in_place_same_slice(&mut new_bases, &instr);
                    instr.clear();
                    number_of_bases_in_batch = 0;
                }
            } else {
                bucket_positions[new_len] = bucket_positions[global_counter];
                new_len += 1;
            }
            global_counter += 1;
        }
        // If there are any remaining unprocessed instructions, proceed to perform batch addition.
        if !instr.is_empty() {
            G::batch_add_in_place_same_slice(&mut new_bases, &instr);
            instr.clear();
        }
        global_counter = 0;
        number_of_bases_in_batch = 0;
        local_counter = 1;
        num_scalars = new_len;
        new_len = 0;
    }

    let mut res = vec![G::zero(); num_buckets];
    for bucket_position in bucket_positions.iter().take(num_scalars) {
        res[bucket_position.bucket_index as usize] = new_bases[bucket_position.scalar_index as usize];
    }
    res
}

#[inline]
fn batched_window<G: AffineCurve>(
    bases: &[G],
    scalars: &[<G::ScalarField as PrimeField>::BigInteger],
    w_start: usize,
    c: usize,
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

    let buckets = batch_add::<G>(num_buckets, bases, &mut bucket_positions);

    let mut res = G::Projective::zero();
    let mut running_sum = G::Projective::zero();
    for b in buckets.into_iter().rev() {
        running_sum.add_assign_mixed(&b);
        res += &running_sum;
    }

    (res, window_size)
}

pub fn msm<G: AffineCurve>(bases: &[G], scalars: &[<G::ScalarField as PrimeField>::BigInteger]) -> G::Projective {
    // Determine the bucket size `c` (chosen empirically).
    let c = match scalars.len() < 32 {
        true => 1,
        false => crate::msm::ln_without_floats(scalars.len()) + 2,
    };

    let num_bits = <G::ScalarField as PrimeField>::size_in_bits();

    // Each window is of size `c`.
    // We divide up the bits 0..num_bits into windows of size `c`, and
    // in parallel process each such window.
    let window_sums: Vec<_> =
        cfg_into_iter!(0..num_bits).step_by(c).map(|w_start| batched_window(bases, scalars, w_start, c)).collect();

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
