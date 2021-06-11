// Copyright Supranational LLC
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <algorithm>
#include <iostream>
#include <cstring>
#include <immintrin.h>
#include "sn_msm.h"
#include <cmath>

// Calculate the bit mask for each window and store in object
void calc_bit_window_masks(std::vector<BitWindowMask>& bit_masks,
                           size_t num_groups,
                           size_t scalar_bits,
                           size_t c) {
  // Number of windows
  //size_t num_groups = (scalar_bits + c - 1) / c;
  if (bit_masks.size() != num_groups) {
    return;
  }

  // Variables for scalar bit window extraction
  limb_t bit_mask = (1 << c) - 1;
  bool   crosses_limbs = (((sizeof(limb_t) * 8) % c) != 0);
  size_t num_limbs = ceil((double)scalar_bits/8/sizeof(limb_t));

  for (size_t k = 0; k < num_groups; ++k) {
    // Current masks for bit window extraction
    bit_masks[k].index      = (k * c) / (sizeof(limb_t) * 8);
    bit_masks[k].shift      = (k * c) - 
                              (bit_masks[k].index * (sizeof(limb_t) * 8));
    bit_masks[k].mask       = bit_mask << bit_masks[k].shift;
    bit_masks[k].multi_limb = crosses_limbs &&
                              (bit_masks[k].shift > 
                               ((sizeof(limb_t) * 8) - c)) &&
                              (bit_masks[k].index < (num_limbs - 1));
    if (bit_masks[k].multi_limb) {
      bit_masks[k].shift_high = c - (bit_masks[k].shift - 
                                     ((sizeof(limb_t) * 8) - c));
      bit_masks[k].mask_high  = (1 << (bit_masks[k].shift - 
                                       ((sizeof(limb_t) * 8) - c))) - 1;
    }
  }
}

// Encode the scalars to use the subtraction trick used by gurvy
// If the window is larger than 2^(c-1) then borrow 2^c from next window
//  Subtract 2^c from the current window to make it negative
// The negative windows will subtract the base rather than add (neg is cheap)
void encode_scalars(std::vector<blst_scalar>& scalars_out,
                    //const std::vector<blst_scalar>& scalars_in,
                    const blst_scalar* scalars_in,
                    size_t num_pairs,
                    size_t scalar_bits,
                    size_t c) {

  size_t num_groups = (scalar_bits + c - 1) / c;
  std::vector<BitWindowMask> bit_masks(num_groups);
  calc_bit_window_masks(bit_masks, num_groups, scalar_bits, c);

  int bucket_max = (1 << (c - 1));

  //for (auto &b: bit_masks) {
  //  printf("index %ld shift %ld mask %lx\n", b.index, b.shift, b.mask);
  //}

  // Go through each scalar and modify window if needed
  for (size_t i = 0; i < num_pairs; ++i) {
    int carry  = 0;
    int bucket;

    for (auto &bm: bit_masks) {
      bucket = carry;
      carry  = 0;

      // Determine bucket based on value of scalar bits in current window
      bucket += (scalars_in[i][bm.index] & bm.mask) >> bm.shift;
      if (bm.multi_limb) {
        bucket += (scalars_in[i][bm.index + 1] & bm.mask_high)
                  << bm.shift_high;
      }

      if (bucket >= bucket_max) {
        bucket -= (1 << c);
        carry   = 1;
      }

      limb_t window_bits = (limb_t)bucket;
      if (bucket < 0) {
        window_bits = (limb_t)((-bucket - 1) | bucket_max);
        //printf("bucket %x, neg bucket %x Window bits %lx\n", bucket, (-bucket), window_bits);
      }

      scalars_out[i][bm.index] |= (window_bits << bm.shift);
      if (bm.multi_limb) {
        scalars_out[i][bm.index + 1] |= (window_bits >> bm.shift_high);
      }
    }
  }
}

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
