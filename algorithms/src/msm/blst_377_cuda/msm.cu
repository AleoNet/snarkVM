#include "blst_377_ops.h"
#include <stdio.h>

template <size_t scalar_bits, size_t bit_width, size_t num_buckets>
__device__ void msm6_window(blst_p1* output, const blst_p1_affine* bases_in, const blst_scalar* scalars, size_t scalar_len) {
    blst_p1 buckets[num_buckets];
    for (size_t i = 0; i < num_buckets; ++i) {
        memcpy(&buckets[i], &BLS12_377_ZERO_PROJECTIVE, sizeof(blst_p1));
    }

    // Current masks for bit window extraction
    limb_t bit_mask = (1 << bit_width) - 1;
    bool crosses_limbs = (((sizeof(limb_t) * 8) % bit_width) != 0);
    size_t num_limbs = ceil((double)scalar_bits/8/sizeof(limb_t));

    limb_t index = (threadIdx.x * bit_width) / 64;
    size_t shift = (threadIdx.x * bit_width) - (index * (sizeof(limb_t) * 8));
    limb_t mask  = bit_mask << shift;
    bool multi_limb = crosses_limbs &&
                      (shift > ((sizeof(limb_t) * 8) - bit_width)) &&
                      (index < (num_limbs - 1));
    size_t shift_high = 0;
    limb_t mask_high  = 0;
    if (multi_limb) {
      shift_high = bit_width - (shift - ((sizeof(limb_t) * 8) - bit_width));
      mask_high  = (1 << (shift - ((sizeof(limb_t) * 8) - bit_width))) - 1;
    }

    // Loop through all points and add associated point to corresponding bucket
    for (size_t i = 0; i < scalar_len; ++i) {
        limb_t bucket = (scalars[i][index] & mask) >> shift;
        if (multi_limb) {
            bucket += (scalars[i][index + 1] & mask_high) << shift_high;
        }
        // printf("t%i: scalar %llu: bucket=%llu sindex=%llu scalar=%llu base_x=%llu base_y=%llu\n", threadIdx.x, i, bucket, index, scalars[i][index], bases_in[i].X[0], bases_in[i].Y[0]);

        // If no bits are set then skip to next pair
        if (bucket == 0) {
            continue;
        }

        // todo: cost of subtraction probably isnt worth it
        // limb_t prebucket = buckets[bucket - 1].X[0];
        blstv2_add_affine_to_projective(&(buckets[bucket - 1]), &(buckets[bucket - 1]), &(bases_in[i]));
        // printf("c-t%i: sindex=%llu ssindex=%llu scalar=%llu base_x=%llu output=%llu prebucket=%llu\n", threadIdx.x, i, index, scalars[i][index], bases_in[i].X[0], buckets[bucket - 1].X[0], prebucket);
    }

    blst_p1 running_sum;
    memcpy(&running_sum, &BLS12_377_ZERO_PROJECTIVE, sizeof(blst_p1));
    blst_p1 out;
    memcpy(&out, &BLS12_377_ZERO_PROJECTIVE, sizeof(blst_p1));

    for (int i = num_buckets - 1; i >= 0; i--) {
        // printf("c-t%i:pre: bucket %i: bx=%llu by=%llu bz=%llu\n", threadIdx.x, i, buckets[i].X[0], buckets[i].Y[0], buckets[i].Z[0]);
        blst_p1_affine affine;
        blst_p1_projective_into_affine(&affine, &(buckets[i]));
        // printf("c-t%i:affine: bucket %i: ax=%llu ay=%llu\n", threadIdx.x, i, affine.X[0], affine.Y[0]);
        blstv2_add_affine_to_projective(&running_sum, &running_sum, &affine);
        // printf("c-t%i:added: bucket %i: sx=%llu sy=%llu sz=%llu\n", threadIdx.x, i, running_sum.X[0], running_sum.Y[0], running_sum.Z[0]);
        blst_p1_add_or_double(&out, &out, &running_sum);
        // printf("c-t%i:committed: bucket %i: ox=%llu oy=%llu oz=%llu\n", threadIdx.x, i, out.X[0], out.Y[0], out.Z[0]);
    }
    memcpy(&output[threadIdx.x], &out, sizeof(blst_p1));
}

extern "C" __global__ void msm6_window_253_1(blst_p1* output, const blst_p1_affine* bases_in, const blst_scalar* scalars, size_t scalar_len) {
  msm6_window<253, 1, 1>(output, bases_in, scalars, scalar_len);
}
