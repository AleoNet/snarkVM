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
    blstv2_add_projective_to_projective(ret, &a[0], &a[1]);
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
    blst_inverse(ret, a);
}

