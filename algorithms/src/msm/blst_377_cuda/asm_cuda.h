#include "types.h"

#pragma once

__device__ void mul_mont_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p, limb_t p_inv);

__device__ void sqr_mont_384(blst_fp ret, const blst_fp a, const blst_fp p, limb_t p_inv);

__device__ void add_mod_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p);

__device__ void sub_mod_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p);

__device__ void sub_mod_384_unsafe(blst_fp ret, const blst_fp a, const blst_fp b);

__device__ void add_mod_384_unsafe(blst_fp ret, const blst_fp a, const blst_fp b);

__device__ void div_by_2_mod_384(blst_fp ret, const blst_fp a);

__device__ void cneg_mod_384(blst_fp ret, const blst_fp a, bool flag, const blst_fp p);

__device__ static inline int is_gt_384(const blst_fp left, const blst_fp right) {
    for (int i = 5; i >= 0; --i) {
        if (left[i] < right[i]) {
            return 0;
        } else if (left[i] > right[i]) {
            return 1;
        }
    }
    return 0;
}
