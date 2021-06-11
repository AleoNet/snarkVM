#include "blst_377_ops.h"
#include <stdio.h>
#include <stdint.h>

static const uint32_t WINDOW_SIZE = 32;
static const uint32_t BLST_WIDTH = 253;

extern "C" __global__ void msm6_pixel(blst_p1* bucket_lists, const blst_p1_affine* bases_in, const blst_scalar* scalars, const uint32_t* window_lengths, const uint32_t window_count) {
    limb_t index = threadIdx.x / 64;
    size_t shift = threadIdx.x - (index * 64);
    // printf("c-%i:%i: running\n", threadIdx.x, blockIdx.x);

    blst_p1 bucket;
    memcpy(&bucket, &BLS12_377_ZERO_PROJECTIVE, sizeof(blst_p1));

    uint32_t window_start = WINDOW_SIZE * blockIdx.x;
    uint32_t window_end = window_start + window_lengths[blockIdx.x];
    // printf("c-%i:%i: windows %u -> %u\n", threadIdx.x, blockIdx.x, window_start, window_start + window_lengths[blockIdx.x]);
    for (uint32_t i = window_start; i < window_end; ++i) {
        // printf("c-%i:%i: doing %lu\n", threadIdx.x, blockIdx.x, i);
        limb_t bit = (scalars[i][index] >> shift) & 1;
        if (bit == 0) {
            continue;
        }
        blstv2_add_affine_to_projective(&bucket, &bucket, &(bases_in[i]));
    }

    memcpy(&bucket_lists[threadIdx.x * window_count + blockIdx.x], &bucket, sizeof(blst_p1));
}

extern "C" __global__ void msm6_collapse_rows(blst_p1* target, const blst_p1* bucket_lists, const uint32_t window_count) {
    blst_p1 temp_target;
    uint32_t base = threadIdx.x * window_count;
    uint32_t term = base + window_count;
    memcpy(&temp_target, &bucket_lists[base], sizeof(blst_p1));

    for (uint32_t i = base + 1; i < term; ++i) {
        blst_p1_add_or_double(&temp_target, &temp_target, &bucket_lists[i]);
    }
    
    memcpy(&target[threadIdx.x], &temp_target, sizeof(blst_p1));
}

// extern "C" __global__ void msm6_window_253_1(blst_p1* output, const blst_p1* bucket_list) {
//     blst_p1 running_sum;
//     memcpy(&running_sum, &BLS12_377_ZERO_PROJECTIVE, sizeof(blst_p1));
//     blst_p1 out;
//     memcpy(&out, &BLS12_377_ZERO_PROJECTIVE, sizeof(blst_p1));

//     // printf("c-t%i:pre: bucket %i: bx=%llu by=%llu bz=%llu\n", threadIdx.x, i, buckets[i].X[0], buckets[i].Y[0], buckets[i].Z[0]);
//     blst_p1_affine affine;
//     blst_p1_projective_into_affine(&affine, &bucket);
//     // printf("c-t%i:affine: bucket %i: ax=%llu ay=%llu\n", threadIdx.x, i, affine.X[0], affine.Y[0]);
//     blstv2_add_affine_to_projective(&running_sum, &running_sum, &affine);
//     // printf("c-t%i:added: bucket %i: sx=%llu sy=%llu sz=%llu\n", threadIdx.x, i, running_sum.X[0], running_sum.Y[0], running_sum.Z[0]);
//     blst_p1_add_or_double(&out, &out, &running_sum);
//     // printf("c-t%i:committed: bucket %i: ox=%llu oy=%llu oz=%llu\n", threadIdx.x, i, out.X[0], out.Y[0], out.Z[0]);
//     memcpy(&output[threadIdx.x], &out, sizeof(blst_p1));
// }

/*

extern "C" __global__ void msm6_window_253_1(blst_p1* output, const blst_p1_affine* bases_in, const blst_scalar* scalars, size_t scalar_len) {
    blst_p1 bucket;
    memcpy(&bucket, &BLS12_377_ZERO_PROJECTIVE, sizeof(blst_p1));

    limb_t index = threadIdx.x / 64;
    size_t shift = threadIdx.x - (index * 64);

    // Loop through all points and add associated point to corresponding bucket
    for (size_t i = 0; i < scalar_len; ++i) {
        limb_t bit = (scalars[i][index] >> shift) & 1;
        // printf("t%i: scalar %llu: bucket=%llu sindex=%llu scalar=%llu base_x=%llu base_y=%llu\n", threadIdx.x, i, bucket, index, scalars[i][index], bases_in[i].X[0], bases_in[i].Y[0]);

        // If no bits are set then skip to next pair
        if (bit == 0) {
            continue;
        }

        // todo: cost of subtraction probably isnt worth it
        // limb_t prebucket = buckets[bucket - 1].X[0];
        blstv2_add_affine_to_projective(&bucket, &bucket, &(bases_in[i]));
        // printf("c-t%i: sindex=%llu ssindex=%llu scalar=%llu base_x=%llu output=%llu prebucket=%llu\n", threadIdx.x, i, index, scalars[i][index], bases_in[i].X[0], buckets[bucket - 1].X[0], prebucket);
    }

    blst_p1 running_sum;
    memcpy(&running_sum, &BLS12_377_ZERO_PROJECTIVE, sizeof(blst_p1));
    blst_p1 out;
    memcpy(&out, &BLS12_377_ZERO_PROJECTIVE, sizeof(blst_p1));

    // printf("c-t%i:pre: bucket %i: bx=%llu by=%llu bz=%llu\n", threadIdx.x, i, buckets[i].X[0], buckets[i].Y[0], buckets[i].Z[0]);
    blst_p1_affine affine;
    blst_p1_projective_into_affine(&affine, &bucket);
    // printf("c-t%i:affine: bucket %i: ax=%llu ay=%llu\n", threadIdx.x, i, affine.X[0], affine.Y[0]);
    blstv2_add_affine_to_projective(&running_sum, &running_sum, &affine);
    // printf("c-t%i:added: bucket %i: sx=%llu sy=%llu sz=%llu\n", threadIdx.x, i, running_sum.X[0], running_sum.Y[0], running_sum.Z[0]);
    blst_p1_add_or_double(&out, &out, &running_sum);
    // printf("c-t%i:committed: bucket %i: ox=%llu oy=%llu oz=%llu\n", threadIdx.x, i, out.X[0], out.Y[0], out.Z[0]);
    memcpy(&output[threadIdx.x], &out, sizeof(blst_p1));
}

*/