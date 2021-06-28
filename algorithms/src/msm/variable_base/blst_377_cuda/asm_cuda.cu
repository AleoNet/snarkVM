#include <string.h>
#include <cuda_runtime.h>
#include <stdio.h>
#include "types.h"
#include "asm_cuda.h"

__device__ static inline int is_ge_384(const blst_fp left, const blst_fp right) {
    for (int i = 5; i >= 0; --i) {
        if (left[i] < right[i]) {
            return 0;
        } else if (left[i] > right[i]) {
            return 1;
        }
    }
    return 1;
}

__device__ static inline void sub_mod_384_unchecked(blst_fp ret, const blst_fp a, const blst_fp b) {
   asm(
      "sub.cc.u64 %0, %6, %12;\n\t"
      "subc.cc.u64 %1, %7, %13;\n\t"
      "subc.cc.u64 %2, %8, %14;\n\t"
      "subc.cc.u64 %3, %9, %15;\n\t"
      "subc.cc.u64 %4, %10, %16;\n\t"
      "subc.u64 %5, %11, %17;"
      : "=l"(ret[0]),
      "=l"(ret[1]),
      "=l"(ret[2]),
      "=l"(ret[3]),
      "=l"(ret[4]),
      "=l"(ret[5])
      : "l"(a[0]),
      "l"(a[1]),
      "l"(a[2]),
      "l"(a[3]),
      "l"(a[4]),
      "l"(a[5]),
      "l"(b[0]),
      "l"(b[1]),
      "l"(b[2]),
      "l"(b[3]),
      "l"(b[4]),
      "l"(b[5])
    );
    // return cf != 0?
}

__device__ static inline void reduce(blst_fp x, const blst_fp p) {
    if (is_ge_384(x, p)) {
        blst_fp x_sub;
        sub_mod_384_unchecked(x_sub, x, p);
        memcpy(x, x_sub, sizeof(blst_fp));
    }
}

// The Montgomery reduction here is based on Algorithm 14.32 in
// Handbook of Applied Cryptography
// <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.
__device__ static inline void mont_384(blst_fp ret, limb_t r[12], const blst_fp p, const limb_t p_inv) {
    // printf("c-t%i:0: %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]);
    limb_t k = r[0] * p_inv;
    
    limb_t cross_carry = 0;

    asm(
      "{\n\t"
      ".reg .u64 c;\n\t"
      ".reg .u64 t;\n\t"
      ".reg .u64 nc;\n\t"

      "mad.lo.cc.u64 c, %14, %8, %0;\n\t"
      "madc.hi.cc.u64 c, %14, %8, 0;\n\t"
      
      "addc.cc.u64 t, %1, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %1, %14, %9, t;\n\t"
      "madc.hi.cc.u64 c, %14, %9, nc;\n\t"

      "addc.cc.u64 t, %2, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %2, %14, %10, t;\n\t"
      "madc.hi.cc.u64 c, %14, %10, nc;\n\t"

      "addc.cc.u64 t, %3, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %3, %14, %11, t;\n\t"
      "madc.hi.cc.u64 c, %14, %11, nc;\n\t"

      "addc.cc.u64 t, %4, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %4, %14, %12, t;\n\t"
      "madc.hi.cc.u64 c, %14, %12, nc;\n\t"

      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %14, %13, t;\n\t"
      "madc.hi.cc.u64 c, %14, %13, nc;\n\t"

      "addc.cc.u64 %6, %6, c;\n\t"
      "addc.u64 %7, 0, 0;\n\t"
      "}"
      : "+l"(r[0]),
      "+l"(r[1]),
      "+l"(r[2]),
      "+l"(r[3]),
      "+l"(r[4]),
      "+l"(r[5]),
      "+l"(r[6]),
      "=l"(cross_carry)
      : "l"(p[0]),
      "l"(p[1]),
      "l"(p[2]),
      "l"(p[3]),
      "l"(p[4]),
      "l"(p[5]),
      "l"(k)
    );

    // printf("c-t%i:1: %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]);

    k = r[1] * p_inv;

    asm(
      "{\n\t"
      ".reg .u64 c;\n\t"
      ".reg .u64 t;\n\t"
      ".reg .u64 nc;\n\t"

      "mad.lo.cc.u64 c, %14, %8, %0;\n\t"
      "madc.hi.cc.u64 c, %14, %8, 0;\n\t"
      
      "addc.cc.u64 t, %1, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %1, %14, %9, t;\n\t"
      "madc.hi.cc.u64 c, %14, %9, nc;\n\t"

      "addc.cc.u64 t, %2, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %2, %14, %10, t;\n\t"
      "madc.hi.cc.u64 c, %14, %10, nc;\n\t"

      "addc.cc.u64 t, %3, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %3, %14, %11, t;\n\t"
      "madc.hi.cc.u64 c, %14, %11, nc;\n\t"

      "addc.cc.u64 t, %4, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %4, %14, %12, t;\n\t"
      "madc.hi.cc.u64 c, %14, %12, nc;\n\t"

      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %14, %13, t;\n\t"
      "madc.hi.cc.u64 c, %14, %13, nc;\n\t"

      "addc.cc.u64 c, c, %7;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "addc.cc.u64 %6, %6, c;\n\t"
      "addc.u64 %7, nc, 0;\n\t"
      "}"
      : "+l"(r[1]),
      "+l"(r[2]),
      "+l"(r[3]),
      "+l"(r[4]),
      "+l"(r[5]),
      "+l"(r[6]),
      "+l"(r[7]),
      "+l"(cross_carry)
      : "l"(p[0]),
      "l"(p[1]),
      "l"(p[2]),
      "l"(p[3]),
      "l"(p[4]),
      "l"(p[5]),
      "l"(k)
    );

    // printf("c-t%i:2: %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]);
    k = r[2] * p_inv;

    asm(
      "{\n\t"
      ".reg .u64 c;\n\t"
      ".reg .u64 t;\n\t"
      ".reg .u64 nc;\n\t"
      
      "mad.lo.cc.u64 c, %14, %8, %0;\n\t"
      "madc.hi.cc.u64 c, %14, %8, 0;\n\t"
      
      "addc.cc.u64 t, %1, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %1, %14, %9, t;\n\t"
      "madc.hi.cc.u64 c, %14, %9, nc;\n\t"

      "addc.cc.u64 t, %2, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %2, %14, %10, t;\n\t"
      "madc.hi.cc.u64 c, %14, %10, nc;\n\t"

      "addc.cc.u64 t, %3, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %3, %14, %11, t;\n\t"
      "madc.hi.cc.u64 c, %14, %11, nc;\n\t"

      "addc.cc.u64 t, %4, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %4, %14, %12, t;\n\t"
      "madc.hi.cc.u64 c, %14, %12, nc;\n\t"

      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %14, %13, t;\n\t"
      "madc.hi.cc.u64 c, %14, %13, nc;\n\t"

      "addc.cc.u64 c, c, %7;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "addc.cc.u64 %6, %6, c;\n\t"
      "addc.u64 %7, nc, 0;\n\t"
      "}"
      : "+l"(r[2]),
      "+l"(r[3]),
      "+l"(r[4]),
      "+l"(r[5]),
      "+l"(r[6]),
      "+l"(r[7]),
      "+l"(r[8]),
      "+l"(cross_carry)
      : "l"(p[0]),
      "l"(p[1]),
      "l"(p[2]),
      "l"(p[3]),
      "l"(p[4]),
      "l"(p[5]),
      "l"(k)
    );

    // printf("c-t%i:3: %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]);

    k = r[3] * p_inv;

    asm(
      "{\n\t"
      ".reg .u64 c;\n\t"
      ".reg .u64 t;\n\t"
      ".reg .u64 nc;\n\t"
      
      "mad.lo.cc.u64 c, %14, %8, %0;\n\t"
      "madc.hi.cc.u64 c, %14, %8, 0;\n\t"
      
      "addc.cc.u64 t, %1, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %1, %14, %9, t;\n\t"
      "madc.hi.cc.u64 c, %14, %9, nc;\n\t"

      "addc.cc.u64 t, %2, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %2, %14, %10, t;\n\t"
      "madc.hi.cc.u64 c, %14, %10, nc;\n\t"

      "addc.cc.u64 t, %3, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %3, %14, %11, t;\n\t"
      "madc.hi.cc.u64 c, %14, %11, nc;\n\t"

      "addc.cc.u64 t, %4, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %4, %14, %12, t;\n\t"
      "madc.hi.cc.u64 c, %14, %12, nc;\n\t"

      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %14, %13, t;\n\t"
      "madc.hi.cc.u64 c, %14, %13, nc;\n\t"

      "addc.cc.u64 c, c, %7;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "addc.cc.u64 %6, %6, c;\n\t"
      "addc.u64 %7, nc, 0;\n\t"
      "}"
      : "+l"(r[3]),
      "+l"(r[4]),
      "+l"(r[5]),
      "+l"(r[6]),
      "+l"(r[7]),
      "+l"(r[8]),
      "+l"(r[9]),
      "+l"(cross_carry)
      : "l"(p[0]),
      "l"(p[1]),
      "l"(p[2]),
      "l"(p[3]),
      "l"(p[4]),
      "l"(p[5]),
      "l"(k)
    );

    // printf("c-t%i:4: %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]);
    k = r[4] * p_inv;

    asm(
      "{\n\t"
      ".reg .u64 c;\n\t"
      ".reg .u64 t;\n\t"
      ".reg .u64 nc;\n\t"
      
      "mad.lo.cc.u64 c, %14, %8, %0;\n\t"
      "madc.hi.cc.u64 c, %14, %8, 0;\n\t"
      
      "addc.cc.u64 t, %1, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %1, %14, %9, t;\n\t"
      "madc.hi.cc.u64 c, %14, %9, nc;\n\t"

      "addc.cc.u64 t, %2, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %2, %14, %10, t;\n\t"
      "madc.hi.cc.u64 c, %14, %10, nc;\n\t"

      "addc.cc.u64 t, %3, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %3, %14, %11, t;\n\t"
      "madc.hi.cc.u64 c, %14, %11, nc;\n\t"

      "addc.cc.u64 t, %4, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %4, %14, %12, t;\n\t"
      "madc.hi.cc.u64 c, %14, %12, nc;\n\t"

      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %14, %13, t;\n\t"
      "madc.hi.cc.u64 c, %14, %13, nc;\n\t"

      "addc.cc.u64 c, c, %7;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "addc.cc.u64 %6, %6, c;\n\t"
      "addc.u64 %7, nc, 0;\n\t"
      "}"
      : "+l"(r[4]),
      "+l"(r[5]),
      "+l"(r[6]),
      "+l"(r[7]),
      "+l"(r[8]),
      "+l"(r[9]),
      "+l"(r[10]),
      "+l"(cross_carry)
      : "l"(p[0]),
      "l"(p[1]),
      "l"(p[2]),
      "l"(p[3]),
      "l"(p[4]),
      "l"(p[5]),
      "l"(k)
    );

    // printf("c-t%i:5: %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]);
    k = r[5] * p_inv;

    asm(
      "{\n\t"
      ".reg .u64 c;\n\t"
      ".reg .u64 t;\n\t"
      ".reg .u64 nc;\n\t"
      
      "mad.lo.cc.u64 c, %14, %8, %0;\n\t"
      "madc.hi.cc.u64 c, %14, %8, 0;\n\t"
      
      "addc.cc.u64 t, %1, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %1, %14, %9, t;\n\t"
      "madc.hi.cc.u64 c, %14, %9, nc;\n\t"

      "addc.cc.u64 t, %2, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %2, %14, %10, t;\n\t"
      "madc.hi.cc.u64 c, %14, %10, nc;\n\t"

      "addc.cc.u64 t, %3, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %3, %14, %11, t;\n\t"
      "madc.hi.cc.u64 c, %14, %11, nc;\n\t"

      "addc.cc.u64 t, %4, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %4, %14, %12, t;\n\t"
      "madc.hi.cc.u64 c, %14, %12, nc;\n\t"

      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %14, %13, t;\n\t"
      "madc.hi.cc.u64 c, %14, %13, nc;\n\t"

      "addc.cc.u64 c, c, %7;\n\t"
      // "addc.u64 nc, 0, 0;\n\t" if we dont want to clobber cross_carry we need this
      "add.u64 %6, %6, c;\n\t" // and this to be add.cc
      // "addc.u64 %7, nc, 0;\n\t" and this
      "}"
      : "+l"(r[5]),
      "+l"(r[6]),
      "+l"(r[7]),
      "+l"(r[8]),
      "+l"(r[9]),
      "+l"(r[10]),
      "+l"(r[11])
      : "l"(cross_carry),
      "l"(p[0]),
      "l"(p[1]),
      "l"(p[2]),
      "l"(p[3]),
      "l"(p[4]),
      "l"(p[5]),
      "l"(k)
    );

    // printf("c-t%i:6: %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]);

    memcpy(ret, r + 6, sizeof(limb_t) * 6);
    reduce(ret, p);
}

__device__ void mul_mont_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p, limb_t p_inv) {
    limb_t r[12];

    asm(
      "{\n\t"
      ".reg .u64 c;\n\t"
      ".reg .u64 nc;\n\t"
      ".reg .u64 t;\n\t"
      
      "mad.lo.cc.u64 %0, %12, %18, 0;\n\t"
      "madc.hi.cc.u64 c, %12, %18, 0;\n\t"
      
      "madc.lo.cc.u64 %1, %12, %19, c;\n\t"
      "madc.hi.cc.u64 c, %12, %19, 0;\n\t"

      "madc.lo.cc.u64 %2, %12, %20, c;\n\t"
      "madc.hi.cc.u64 c, %12, %20, 0;\n\t"

      "madc.lo.cc.u64 %3, %12, %21, c;\n\t"
      "madc.hi.cc.u64 c, %12, %21, 0;\n\t"

      "madc.lo.cc.u64 %4, %12, %22, c;\n\t"
      "madc.hi.cc.u64 c, %12, %22, 0;\n\t"

      "madc.lo.cc.u64 %5, %12, %23, c;\n\t"
      "madc.hi.u64 %6, %12, %23, 0;\n\t"


      "mad.lo.cc.u64 %1, %13, %18, %1;\n\t"
      "madc.hi.cc.u64 c, %13, %18, 0;\n\t"
      
      "addc.cc.u64 t, %2, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %2, %13, %19, t;\n\t"
      "madc.hi.cc.u64 c, %13, %19, nc;\n\t"

      "addc.cc.u64 t, %3, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %3, %13, %20, t;\n\t"
      "madc.hi.cc.u64 c, %13, %20, nc;\n\t"

      "addc.cc.u64 t, %4, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %4, %13, %21, t;\n\t"
      "madc.hi.cc.u64 c, %13, %21, nc;\n\t"

      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %13, %22, t;\n\t"
      "madc.hi.cc.u64 c, %13, %22, nc;\n\t"

      "addc.cc.u64 t, %6, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %6, %13, %23, t;\n\t"
      "madc.hi.u64 %7, %13, %23, nc;\n\t"


      "mad.lo.cc.u64 %2, %14, %18, %2;\n\t"
      "madc.hi.cc.u64 c, %14, %18, 0;\n\t"
      
      "addc.cc.u64 t, %3, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %3, %14, %19, t;\n\t"
      "madc.hi.cc.u64 c, %14, %19, nc;\n\t"
      
      "addc.cc.u64 t, %4, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %4, %14, %20, t;\n\t"
      "madc.hi.cc.u64 c, %14, %20, nc;\n\t"

      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %14, %21, t;\n\t"
      "madc.hi.cc.u64 c, %14, %21, nc;\n\t"

      "addc.cc.u64 t, %6, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %6, %14, %22, t;\n\t"
      "madc.hi.cc.u64 c, %14, %22, nc;\n\t"

      "addc.cc.u64 t, %7, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %7, %14, %23, t;\n\t"
      "madc.hi.u64 %8, %14, %23, nc;\n\t"



      "mad.lo.cc.u64 %3, %15, %18, %3;\n\t"
      "madc.hi.cc.u64 c, %15, %18, 0;\n\t"
      
      "addc.cc.u64 t, %4, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %4, %15, %19, t;\n\t"
      "madc.hi.cc.u64 c, %15, %19, nc;\n\t"
      
      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %15, %20, t;\n\t"
      "madc.hi.cc.u64 c, %15, %20, nc;\n\t"
      
      "addc.cc.u64 t, %6, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %6, %15, %21, t;\n\t"
      "madc.hi.cc.u64 c, %15, %21, nc;\n\t"
      
      "addc.cc.u64 t, %7, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %7, %15, %22, t;\n\t"
      "madc.hi.cc.u64 c, %15, %22, nc;\n\t"
      
      "addc.cc.u64 t, %8, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %8, %15, %23, t;\n\t"
      "madc.hi.u64 %9, %15, %23, nc;\n\t"
      



      "mad.lo.cc.u64 %4, %16, %18, %4;\n\t"
      "madc.hi.cc.u64 c, %16, %18, 0;\n\t"
      
      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %16, %19, t;\n\t"
      "madc.hi.cc.u64 c, %16, %19, nc;\n\t"
      
      "addc.cc.u64 t, %6, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %6, %16, %20, t;\n\t"
      "madc.hi.cc.u64 c, %16, %20, nc;\n\t"
      
      "addc.cc.u64 t, %7, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %7, %16, %21, t;\n\t"
      "madc.hi.cc.u64 c, %16, %21, nc;\n\t"
      
      "addc.cc.u64 t, %8, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %8, %16, %22, t;\n\t"
      "madc.hi.cc.u64 c, %16, %22, nc;\n\t"
      
      "addc.cc.u64 t, %9, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %9, %16, %23, t;\n\t"
      "madc.hi.u64 %10, %16, %23, nc;\n\t"
      


      "mad.lo.cc.u64 %5, %17, %18, %5;\n\t"
      "madc.hi.cc.u64 c, %17, %18, 0;\n\t"
      
      "addc.cc.u64 t, %6, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %6, %17, %19, t;\n\t"
      "madc.hi.cc.u64 c, %17, %19, nc;\n\t"
      
      "addc.cc.u64 t, %7, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %7, %17, %20, t;\n\t"
      "madc.hi.cc.u64 c, %17, %20, nc;\n\t"
      
      "addc.cc.u64 t, %8, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %8, %17, %21, t;\n\t"
      "madc.hi.cc.u64 c, %17, %21, nc;\n\t"
      
      "addc.cc.u64 t, %9, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %9, %17, %22, t;\n\t"
      "madc.hi.cc.u64 c, %17, %22, nc;\n\t"
      
      "addc.cc.u64 t, %10, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %10, %17, %23, t;\n\t"
      "madc.hi.u64 %11, %17, %23, nc;\n\t"

      "}"
      : "+l"(r[0]),
      "+l"(r[1]),
      "+l"(r[2]),
      "+l"(r[3]),
      "+l"(r[4]),
      "+l"(r[5]),
      "+l"(r[6]),
      "+l"(r[7]),
      "+l"(r[8]),
      "+l"(r[9]),
      "+l"(r[10]),
      "+l"(r[11])
      : "l"(a[0]),
      "l"(a[1]),
      "l"(a[2]),
      "l"(a[3]),
      "l"(a[4]),
      "l"(a[5]),
      "l"(b[0]),
      "l"(b[1]),
      "l"(b[2]),
      "l"(b[3]),
      "l"(b[4]),
      "l"(b[5])
    );
    
    mont_384(ret, r, p, p_inv);
}

__device__ void sqr_mont_384(blst_fp ret, const blst_fp a, const blst_fp p, limb_t p_inv) {
    limb_t r[12];

    asm(
      "{\n\t"
      ".reg .u64 c;\n\t"
      ".reg .u64 nc;\n\t"
      ".reg .u64 t;\n\t"

      "mad.lo.cc.u64 %1, %12, %13, 0;\n\t"
      "madc.hi.cc.u64 c, %12, %13, 0;\n\t"

      "madc.lo.cc.u64 %2, %12, %14, c;\n\t"
      "madc.hi.cc.u64 c, %12, %14, 0;\n\t"

      "madc.lo.cc.u64 %3, %12, %15, c;\n\t"
      "madc.hi.cc.u64 c, %12, %15, 0;\n\t"

      "madc.lo.cc.u64 %4, %12, %16, c;\n\t"
      "madc.hi.cc.u64 c, %12, %16, 0;\n\t"

      "madc.lo.cc.u64 %5, %12, %17, c;\n\t"
      "madc.hi.u64 %6, %12, %17, 0;\n\t"

      "mad.lo.cc.u64 %3, %13, %14, %3;\n\t"
      "madc.hi.cc.u64 c, %13, %14, 0;\n\t"
      
      "addc.cc.u64 t, %4, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %4, %13, %15, t;\n\t"
      "madc.hi.cc.u64 c, %13, %15, nc;\n\t"

      "addc.cc.u64 t, %5, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %5, %13, %16, t;\n\t"
      "madc.hi.cc.u64 c, %13, %16, nc;\n\t"

      "addc.cc.u64 t, %6, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %6, %13, %17, t;\n\t"
      "madc.hi.u64 %7, %13, %17, nc;\n\t"



      "mad.lo.cc.u64 %5, %14, %15, %5;\n\t"
      "madc.hi.cc.u64 c, %14, %15, 0;\n\t"
      
      "addc.cc.u64 t, %6, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %6, %14, %16, t;\n\t"
      "madc.hi.cc.u64 c, %14, %16, nc;\n\t"
      
      "addc.cc.u64 t, %7, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %7, %14, %17, t;\n\t"
      "madc.hi.u64 %8, %14, %17, nc;\n\t"




      "mad.lo.cc.u64 %7, %15, %16, %7;\n\t"
      "madc.hi.cc.u64 c, %15, %16, 0;\n\t"
      
      "addc.cc.u64 t, %8, c;\n\t"
      "addc.u64 nc, 0, 0;\n\t"
      "mad.lo.cc.u64 %8, %15, %17, t;\n\t"
      "madc.hi.u64 %9, %15, %17, nc;\n\t"
      


      "mad.lo.cc.u64 %9, %16, %17, %9;\n\t"
      "madc.hi.u64 %10, %16, %17, 0;\n\t"

      "}"
      : "+l"(r[0]),
      "+l"(r[1]),
      "+l"(r[2]),
      "+l"(r[3]),
      "+l"(r[4]),
      "+l"(r[5]),
      "+l"(r[6]),
      "+l"(r[7]),
      "+l"(r[8]),
      "+l"(r[9]),
      "+l"(r[10]),
      "+l"(r[11])
      : "l"(a[0]),
      "l"(a[1]),
      "l"(a[2]),
      "l"(a[3]),
      "l"(a[4]),
      "l"(a[5])
    );

    // printf("c-t%i:0: X, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, X\n", threadIdx.x, r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10]);

    r[11] = r[10] >> 63;
    r[10] = (r[10] << 1) | (r[9] >> 63);
    r[9] = (r[9] << 1) | (r[8] >> 63);
    r[8] = (r[8] << 1) | (r[7] >> 63);
    r[7] = (r[7] << 1) | (r[6] >> 63);
    r[6] = (r[6] << 1) | (r[5] >> 63);
    r[5] = (r[5] << 1) | (r[4] >> 63);
    r[4] = (r[4] << 1) | (r[3] >> 63);
    r[3] = (r[3] << 1) | (r[2] >> 63);
    r[2] = (r[2] << 1) | (r[1] >> 63);
    r[1] = r[1] << 1;

    // printf("c-t%i:1: X, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]);

    asm(
      "{\n\t"

      "mad.lo.cc.u64 %0, %12, %12, 0;\n\t"
      "madc.hi.cc.u64 %1, %12, %12, %1;\n\t"

      "madc.lo.cc.u64 %2, %13, %13, %2;\n\t"
      "madc.hi.cc.u64 %3, %13, %13, %3;\n\t"
  
      "madc.lo.cc.u64 %4, %14, %14, %4;\n\t"
      "madc.hi.cc.u64 %5, %14, %14, %5;\n\t"
  
      "madc.lo.cc.u64 %6, %15, %15, %6;\n\t"
      "madc.hi.cc.u64 %7, %15, %15, %7;\n\t"
  
      "madc.lo.cc.u64 %8, %16, %16, %8;\n\t"
      "madc.hi.cc.u64 %9, %16, %16, %9;\n\t"
  
      "madc.lo.cc.u64 %10, %17, %17, %10;\n\t"
      "madc.hi.u64 %11, %17, %17, %11;\n\t"

      "}"
      : "+l"(r[0]),
      "+l"(r[1]),
      "+l"(r[2]),
      "+l"(r[3]),
      "+l"(r[4]),
      "+l"(r[5]),
      "+l"(r[6]),
      "+l"(r[7]),
      "+l"(r[8]),
      "+l"(r[9]),
      "+l"(r[10]),
      "+l"(r[11])
      : "l"(a[0]),
      "l"(a[1]),
      "l"(a[2]),
      "l"(a[3]),
      "l"(a[4]),
      "l"(a[5])
    );
    // printf("c-t%i:2: %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]);

    mont_384(ret, r, p, p_inv);
}


__device__ static inline void add_mod_384_unchecked(blst_fp ret, const blst_fp a, const blst_fp b) {
    asm(
      "add.cc.u64 %0, %6, %12;\n\t"
      "addc.cc.u64 %1, %7, %13;\n\t"
      "addc.cc.u64 %2, %8, %14;\n\t"
      "addc.cc.u64 %3, %9, %15;\n\t"
      "addc.cc.u64 %4, %10, %16;\n\t"
      "addc.u64 %5, %11, %17;"
      : "=l"(ret[0]),
      "=l"(ret[1]),
      "=l"(ret[2]),
      "=l"(ret[3]),
      "=l"(ret[4]),
      "=l"(ret[5])
      : "l"(a[0]),
      "l"(a[1]),
      "l"(a[2]),
      "l"(a[3]),
      "l"(a[4]),
      "l"(a[5]),
      "l"(b[0]),
      "l"(b[1]),
      "l"(b[2]),
      "l"(b[3]),
      "l"(b[4]),
      "l"(b[5])
    );
    // return cf != 0?
}

__device__ void add_mod_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p) {
    add_mod_384_unchecked(ret, a, b);

    reduce(ret, p);
    // return cf != 0?
}

__device__ void sub_mod_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p) {
    blst_fp added;
    memcpy(added, a, sizeof(blst_fp));
    // printf("pre-sub [%llu, %llu, %llu, %llu, %llu, %llu]\n", added[0], added[1], added[2], added[3], added[4], added[5]);
    if (is_gt_384(b, a)) {
      // printf("sub-preduce [%llu, %llu, %llu, %llu, %llu, %llu] > [%llu, %llu, %llu, %llu, %llu, %llu]\n", b[0], b[1], b[2], b[3], b[4], b[5], added[0], added[1], added[2], added[3], added[4], added[5]);
      add_mod_384_unchecked(added, added, p);
      // printf("sub-postduce [%llu, %llu, %llu, %llu, %llu, %llu]\n", added[0], added[1], added[2], added[3], added[4], added[5]);
    } else {
      // printf("sub-nonduce [%llu, %llu, %llu, %llu, %llu, %llu] <= [%llu, %llu, %llu, %llu, %llu, %llu]\n", b[0], b[1], b[2], b[3], b[4], b[5], added[0], added[1], added[2], added[3], added[4], added[5]);
    }
    sub_mod_384_unchecked(ret, added, b);
    // printf("post-sub [%llu, %llu, %llu, %llu, %llu, %llu]\n", ret[0], ret[1], ret[2], ret[3], ret[4], ret[5]);
    // return cf != 0?
}

__device__ void sub_mod_384_unsafe(blst_fp ret, const blst_fp a, const blst_fp b) {
    sub_mod_384_unchecked(ret, a, b);
    // return cf != 0?
}

__device__ void add_mod_384_unsafe(blst_fp ret, const blst_fp a, const blst_fp b) {
    add_mod_384_unchecked(ret, a, b);
    // return cf != 0?
}

__device__ static inline void _rshift_384(blst_fp ret, const blst_fp value) {
    ret[0] = (value[1] << 63) | (value[0] >> 1);
    ret[1] = (value[2] << 63) | (value[1] >> 1);
    ret[2] = (value[3] << 63) | (value[2] >> 1);
    ret[3] = (value[4] << 63) | (value[3] >> 1);
    ret[4] = (value[5] << 63) | (value[4] >> 1);
    ret[5] = value[5] >> 1;
}

__device__ void div_by_2_mod_384(blst_fp ret, const blst_fp a) {
    _rshift_384(ret, a);
}

__device__ void cneg_mod_384(blst_fp ret, const blst_fp a, bool flag, const blst_fp p) {
    // just let the compiler cmov
    if (flag) {
        sub_mod_384(ret, p, a, p);
    } else {
        memcpy(ret, a, 6 * sizeof(limb_t));
    }
}
