#include "types.h"
#include "asm_cuda.h"
#include "blst_377_ops.h"

extern "C" __global__ void sqr_test(blst_fp ret, const blst_fp a) {
    blst_fp_sqr(ret, a);
}

extern "C" __global__ void add_test(blst_fp ret, const blst_fp* a) {
    blst_fp_add(ret, a[0], a[1]);
}

extern "C" __global__ void add_projective_test(blst_p1* ret, const blst_p1* a) {
    blst_p1_add_projective_to_projective(ret, &a[0], &a[1]);
}

extern "C" __global__ void double_projective_test(blst_p1* ret, const blst_p1* a) {
    blst_p1_double(ret, &a[0]);
}

struct projective_affine {
    blst_p1 projective;
    blst_p1_affine affine;
};

extern "C" __global__ void add_projective_affine_test(blst_p1* ret, const struct projective_affine* a) {
    blst_p1_add_affine_to_projective(ret, &a[0].projective, &a[0].affine);
}

extern "C" __global__ void add_affine_test(blst_p1* ret, const blst_p1_affine* a) {
    blst_p1_add_affines_into_projective(ret, &a[0], &a[1]);
}

extern "C" __global__ void affine_round_trip_test(blst_p1_affine* ret, const blst_p1_affine* a) {
    blst_p1 intermediate;
    blst_p1_add_affine_to_projective(&intermediate, &BLS12_377_ZERO_PROJECTIVE, &a[0]);
    blst_p1_projective_into_affine(ret, &intermediate);
}

extern "C" __global__ void sub_test(blst_fp ret, const blst_fp* a) {
    blst_fp_sub(ret, a[0], a[1]);
}

extern "C" __global__ void mul_test(blst_fp ret, const blst_fp* a) {
    blst_fp_mul(ret, a[0], a[1]);
}

extern "C" __global__ void div2_test(blst_fp ret, const blst_fp a) {
    div_by_2_mod_384(ret, a);
}

extern "C" __global__ void inverse_test(blst_fp ret, const blst_fp a) {
    blst_fp_inverse(ret, a);
}

