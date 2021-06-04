// Copyright Supranational LLC
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <algorithm>
#include <iostream>
#include <cstring>
#include <immintrin.h>
#include "sn_msm.h"
#include <cmath>

/****************************************************************************
 * #6. Pippenger - Gurvy, min branches, Jac Extended, Rust compatible
 ****************************************************************************/
void msm_pippenger_6(blst_p1* result,
                     const rust_p1_affine* bases_in,
                     const blst_scalar* scalars_in,
                     size_t num_pairs,
                     size_t scalar_bits,
                     size_t c) {
  // Normally c (window size) is calculated or empirically set
  // Allow as input to improve benchmark and experiment usage
  std::vector<blst_scalar> encoded_scalars(num_pairs);
  encode_scalars(encoded_scalars, scalars_in, num_pairs, scalar_bits, c);

  // Use input variable scalar_bits rather than finding largest bit length
  size_t num_groups = (scalar_bits + c - 1) / c;

  // Variables for scalar bit window extraction
  limb_t bit_mask = (1 << c) - 1;
  bool   crosses_limbs = (((sizeof(limb_t) * 8) % c) != 0);
  size_t num_limbs = ceil((double)scalar_bits/8/sizeof(limb_t));

  size_t num_buckets = (1 << (c - 1));
  size_t bucket_mask = (1 << (c - 1)) - 1;

  // Has the result been set yet
  bool result_valid = false;
  *result = { { 0 }, { 0 }, { 0 } };
  blst_p1_ext inf = { { 0 }, { 0 }, { 0 }, { 0 } }; // Infinity

  std::vector<blst_p1_ext> buckets(num_buckets);

  // Loop through all windows
  for (size_t k = num_groups - 1; k <= num_groups; k--) {
    // Need to double result c times once set
    if (result_valid == true) {
      for (size_t i = 0; i < c; ++i) {
        blst_p1_double(result, result);
      }
    }

    // Set all buckets to infinity
    std::fill(buckets.begin(), buckets.end(), inf);

    // Current masks for bit window extraction
    size_t index = (k * c) / (sizeof(limb_t) * 8);
    size_t shift = (k * c) - (index * (sizeof(limb_t) * 8));
    limb_t mask  = bit_mask << shift;
    bool multi_limb = crosses_limbs &&
                      (shift > ((sizeof(limb_t) * 8) - c)) &&
                      (index < (num_limbs - 1));
    size_t shift_high = 0;
    limb_t mask_high  = 0;
    if (multi_limb) {
      shift_high = c - (shift - ((sizeof(limb_t) * 8) - c));
      mask_high  = (1 << (shift - ((sizeof(limb_t) * 8) - c))) - 1;
    }

    // Loop through all points and add associated point to corresponding bucket
    for (size_t i = 0; i < num_pairs; ++i) {
      size_t bucket = 0;

      // Determine bucket based on value of scalar bits in current window
      bucket = (encoded_scalars[i][index] & mask) >> shift;
      if (multi_limb) {
        bucket += (encoded_scalars[i][index + 1] & mask_high) << shift_high;
      }

      // If no bits are set then skip to next pair
      if (bucket == 0) {
        continue;
      }

      // Add or assign base to bucket value
      if ((bucket & num_buckets) == 0) {
        blst_p1_ext_add_or_double_affine(&(buckets[bucket - 1]),
                                         &(buckets[bucket - 1]),
                                         &(bases_in[i].p));
      }
      else {
        blst_p1_affine cur_base_neg;
        std::memcpy(&cur_base_neg, &(bases_in[i].p), sizeof(blst_p1_affine));
        blst_fp_cneg(cur_base_neg.Y, cur_base_neg.Y, true);
        blst_p1_ext_add_or_double_affine(&(buckets[bucket & bucket_mask]),
                                         &(buckets[bucket & bucket_mask]),
                                         &(cur_base_neg));
      }
    }

    blst_p1 cur_sum = { { 0 }, { 0 }, { 0 } };

    // Add all the buckets to the result
    blst_p1 cur_bucket;
    for (int i = num_buckets - 1; i >= 0; i--) {
      if (blst_p1_ext_is_inf(&(buckets[i])) == false) {
        blst_p1_from_extended_no_check(&cur_bucket, &(buckets[i]));
        blst_p1_add_or_double(&cur_sum, &cur_sum, &cur_bucket);
        result_valid = true;
      }
      if (result_valid == true) {
        blst_p1_add_or_double(result, result, &cur_sum);
      }
    }
  }
}
