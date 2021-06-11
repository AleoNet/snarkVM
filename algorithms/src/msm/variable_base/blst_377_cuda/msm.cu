#include "blst_377_ops.h"
#include <stdio.h>
#include <stdint.h>

static const uint32_t WINDOW_SIZE = 128;
static const uint32_t BLST_WIDTH = 253;

extern "C" __global__ void msm6_pixel(blst_p1* bucket_lists, const blst_p1_affine* bases_in, const blst_scalar* scalars, const uint32_t* window_lengths, const uint32_t window_count) {
    limb_t index = threadIdx.x / 64;
    size_t shift = threadIdx.x - (index * 64);
    limb_t mask = (limb_t) 1 << (limb_t) shift;

    blst_p1 bucket;
    memcpy(&bucket, &BLS12_377_ZERO_PROJECTIVE, sizeof(blst_p1));

    uint32_t window_start = WINDOW_SIZE * blockIdx.x;
    uint32_t window_end = window_start + window_lengths[blockIdx.x];

    uint32_t activated_bases[WINDOW_SIZE];
    uint32_t activated_base_index = 0;

    // printf("c-%i:%i: windows %u -> %u\n", threadIdx.x, blockIdx.x, window_start, window_start + window_lengths[blockIdx.x]);
    // we delay the actual additions to a second loop because it reduces warp divergence (20% practical gain)
    for (uint32_t i = window_start; i < window_end; ++i) {
        // printf("c-%i:%i: doing %lu\n", threadIdx.x, blockIdx.x, i);
        // limb_t bitw = (scalars[i][index] >> shift) & 1;
        limb_t bit = (scalars[i][index] & mask);
        if (bit == 0) {
            continue;
        }
        activated_bases[activated_base_index++] = i;
    }
    for (uint32_t i = 0; i < activated_base_index; ++i) {
        blst_add_affine_to_projective(&bucket, &bucket, &(bases_in[activated_bases[i]]));
    }

    memcpy(&bucket_lists[threadIdx.x * window_count + blockIdx.x], &bucket, sizeof(blst_p1));
}

extern "C" __global__ void msm6_collapse_rows(blst_p1* target, const blst_p1* bucket_lists, const uint32_t window_count) {
    blst_p1 temp_target;
    uint32_t base = threadIdx.x * window_count;
    uint32_t term = base + window_count;
    memcpy(&temp_target, &bucket_lists[base], sizeof(blst_p1));

    for (uint32_t i = base + 1; i < term; ++i) {
        blst_add_projective_to_projective(&temp_target, &temp_target, &bucket_lists[i]);
    }
    
    memcpy(&target[threadIdx.x], &temp_target, sizeof(blst_p1));
}
