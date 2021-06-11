// Copyright Supranational LLC
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef __SUPRANATIONAL_MSM_H__
#define __SUPRANATIONAL_MSM_H__

#include <vector>
#include "blst_377_ops.h"

// Pippenger bucketing
struct BitWindowMask {
  limb_t mask;
  limb_t mask_high;
  size_t index; size_t shift; size_t shift_high; bool   multi_limb;
};

void calc_bit_window_masks(std::vector<BitWindowMask>& bit_masks,
                           size_t scalar_bits,
                           size_t c);

typedef struct { blst_p1_affine p; bool inf; } rust_p1_affine;

extern "C" void msm_pippenger_6(blst_p1* result,
                                const rust_p1_affine* bases_in,
                                const blst_scalar* scalars_in,
                                size_t num_pairs,
                                size_t scalar_bits,
                                size_t c);

#endif // __SUPRANATIONAL_MSM_H__
