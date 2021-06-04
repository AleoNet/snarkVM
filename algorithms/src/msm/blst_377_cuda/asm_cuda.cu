#include "blst_377_ops.h"
#include <string.h>
#include <cuda_runtime.h>

__device__ unsigned long long int __umul64hi(unsigned long long int x, unsigned long long int y);

// add two values with carry out
__device__ static inline limb_t __add_cc(limb_t a, limb_t b) {
  limb_t r;

  asm("add.cc.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b));

  return r;
}

// add two values with carry in and out
__device__ static inline limb_t __addc_cc(limb_t a, limb_t b) {
  limb_t r;

  asm("addc.cc.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b));

  return r;
}

// add two values with carry in
__device__ static inline limb_t __addc(limb_t a, limb_t b) {
  limb_t r;

  asm("addc.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b));

  return r;
}

// subtract two values with carry out
__device__ static inline limb_t __sub_cc(limb_t a, limb_t b) {
  limb_t r;

  asm("sub.cc.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b));

  return r;
}

// subtract two values with carry in and out
__device__ static inline limb_t __subc_cc(limb_t a, limb_t b) {
  limb_t r;

  asm("subc.cc.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b));

  return r;
}

// subtract two values with carry in
__device__ static inline limb_t __subc(limb_t a, limb_t b) {
  limb_t r;

  asm("subc.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b));

  return r;
}

// multiply (lo) two values and add another with carry in and out
__device__ static inline limb_t __madc_lo(limb_t a, limb_t b, limb_t c) {
  limb_t r;

  asm("madc.lo.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b) , "l" (c));

  return r;
}

// multiply (hi) two values and add another with carry in and out
__device__ static inline limb_t __madc_hi(limb_t a, limb_t b, limb_t c) {
  limb_t r;

  asm("madc.hi.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b) , "l" (c));

  return r;
}

// multiply (lo) two values and add another with carry in and out
__device__ static inline limb_t __madc_lo_cc(limb_t a, limb_t b, limb_t c) {
  limb_t r;

  asm("madc.lo.cc.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b) , "l" (c));

  return r;
}

// multiply (hi) two values and add another with carry in and out
__device__ static inline limb_t __madc_hi_cc(limb_t a, limb_t b, limb_t c) {
  limb_t r;

  asm("madc.hi.cc.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b) , "l" (c));

  return r;
}


// multiply (lo) two values and add another with carry out
__device__ static inline limb_t __mad_lo_cc(limb_t a, limb_t b, limb_t c) {
  limb_t r;

  asm("mad.lo.cc.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b) , "l" (c));

  return r;
}

// multiply (hi) two values and add another with carry out
__device__ static inline limb_t __mad_hi_cc(limb_t a, limb_t b, limb_t c) {
  limb_t r;

  asm("mad.hi.cc.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b) , "l" (c));

  return r;
}

// multiply (hi) two values and add another
__device__ static inline limb_t __mul_hi(limb_t a, limb_t b) {
  limb_t r;

  asm("mad.hi.u64 %0, %1, %2;" : "=l" (r) : "l" (a) , "l" (b));

  return r;
}

__device__ static inline int is_ge_384(const blst_fp left, const blst_fp right) {
    for (int i = 5; i >= 0; --i) {
        if (left[i] < right[i]) {
            return 0;
        } else if (right[i] > left[i]) {
            return 1;
        }
    }
    return 1;
}

__device__ static inline void sub_mod_384_unchecked(blst_fp ret, const blst_fp a, const blst_fp b) {
    ret[0] = __sub_cc(a[0], b[0]);
    ret[1] = __subc_cc(a[1], b[1]);
    ret[2] = __subc_cc(a[2], b[2]);
    ret[3] = __subc_cc(a[3], b[3]);
    ret[4] = __subc_cc(a[4], b[4]);
    ret[5] = __subc(a[5], b[5]);
    // return cf != 0?
}

__device__ static inline void reduce(blst_fp x, const blst_fp p) {
    blst_fp x_sub;
    sub_mod_384_unchecked(x_sub, x, p);
    if (is_ge_384(x, p)) {
        memcpy(x, x_sub, sizeof(blst_fp));
    }
}

// The Montgomery reduction here is based on Algorithm 14.32 in
// Handbook of Applied Cryptography
// <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.
__device__ static inline void mont_384(blst_fp ret, limb_t r[12], const blst_fp p, const limb_t p_inv) {
    limb_t k = r[0] * p_inv;
    
    __mad_lo_cc(k, p[0], r[0]);
    limb_t carry = __madc_hi_cc(k, p[0], 0);
    r[1] = __addc_cc(__madc_lo_cc(k, p[1], r[1]), carry);
    carry = __madc_hi_cc(k, p[1], 0);
    r[2] = __addc_cc(__madc_lo_cc(k, p[2], r[2]), carry);
    carry = __madc_hi_cc(k, p[2], 0);
    r[3] = __addc_cc(__madc_lo_cc(k, p[3], r[3]), carry);
    carry = __madc_hi_cc(k, p[3], 0);
    r[4] = __addc_cc(__madc_lo_cc(k, p[4], r[4]), carry);
    carry = __madc_hi_cc(k, p[4], 0);
    r[5] = __addc_cc(__madc_lo_cc(k, p[5], r[5]), carry);
    carry = __madc_hi_cc(k, p[5], 0);
    r[6] = __addc_cc(r[6], carry);

    limb_t carry2 = __addc(0, 0);
    k = r[1] * p_inv;
    __mad_lo_cc(k, p[0], r[1]);
    carry = __madc_hi_cc(k, p[0], 0);
    r[2] = __addc_cc(__madc_lo_cc(k, p[1], r[2]), carry);
    carry = __madc_hi_cc(k, p[1], 0);
    r[3] = __addc_cc(__madc_lo_cc(k, p[2], r[3]), carry);
    carry = __madc_hi_cc(k, p[2], 0);
    r[4] = __addc_cc(__madc_lo_cc(k, p[3], r[4]), carry);
    carry = __madc_hi_cc(k, p[3], 0);
    r[5] = __addc_cc(__madc_lo_cc(k, p[4], r[5]), carry);
    carry = __madc_hi_cc(k, p[4], 0);
    r[6] = __addc_cc(__madc_lo_cc(k, p[5], r[6]), carry);
    carry = __madc_hi_cc(k, p[5], 0);
    r[7] = __addc_cc(r[7], carry);

    limb_t carry3 = __addc(0, 0);
    r[7] = __add_cc(r[7], carry2);
    carry2 = __addc(0, 0) + carry3;

    k = r[2] * p_inv;
    __mad_lo_cc(k, p[0], r[2]);
    carry = __madc_hi_cc(k, p[0], 0);
    r[3] = __addc_cc(__madc_lo_cc(k, p[1], r[3]), carry);
    carry = __madc_hi_cc(k, p[1], 0);
    r[4] = __addc_cc(__madc_lo_cc(k, p[2], r[4]), carry);
    carry = __madc_hi_cc(k, p[2], 0);
    r[5] = __addc_cc(__madc_lo_cc(k, p[3], r[5]), carry);
    carry = __madc_hi_cc(k, p[3], 0);
    r[6] = __addc_cc(__madc_lo_cc(k, p[4], r[6]), carry);
    carry = __madc_hi_cc(k, p[4], 0);
    r[7] = __addc_cc(__madc_lo_cc(k, p[5], r[7]), carry);
    carry = __madc_hi_cc(k, p[5], 0);
    r[8] = __addc_cc(r[8], carry);

    carry3 = __addc(0, 0);
    r[8] = __add_cc(r[8], carry2);
    carry2 = __addc(0, 0) + carry3;

    k = r[3] * p_inv;
    __mad_lo_cc(k, p[0], r[3]);
    carry = __madc_hi_cc(k, p[0], 0);
    r[4] = __addc_cc(__madc_lo_cc(k, p[1], r[4]), carry);
    carry = __madc_hi_cc(k, p[1], 0);
    r[5] = __addc_cc(__madc_lo_cc(k, p[2], r[5]), carry);
    carry = __madc_hi_cc(k, p[2], 0);
    r[6] = __addc_cc(__madc_lo_cc(k, p[3], r[6]), carry);
    carry = __madc_hi_cc(k, p[3], 0);
    r[7] = __addc_cc(__madc_lo_cc(k, p[4], r[7]), carry);
    carry = __madc_hi_cc(k, p[4], 0);
    r[8] = __addc_cc(__madc_lo_cc(k, p[5], r[8]), carry);
    carry = __madc_hi_cc(k, p[5], 0);
    r[9] = __addc_cc(r[9], carry);

    carry3 = __addc(0, 0);
    r[9] = __add_cc(r[9], carry2);
    carry2 = __addc(0, 0) + carry3;

    k = r[4] * p_inv;
    __mad_lo_cc(k, p[0], r[4]);
    carry = __madc_hi_cc(k, p[0], 0);
    r[5] = __addc_cc(__madc_lo_cc(k, p[1], r[5]), carry);
    carry = __madc_hi_cc(k, p[1], 0);
    r[6] = __addc_cc(__madc_lo_cc(k, p[2], r[6]), carry);
    carry = __madc_hi_cc(k, p[2], 0);
    r[7] = __addc_cc(__madc_lo_cc(k, p[3], r[7]), carry);
    carry = __madc_hi_cc(k, p[3], 0);
    r[8] = __addc_cc(__madc_lo_cc(k, p[4], r[8]), carry);
    carry = __madc_hi_cc(k, p[4], 0);
    r[9] = __addc_cc(__madc_lo_cc(k, p[5], r[9]), carry);
    carry = __madc_hi_cc(k, p[5], 0);
    r[10] = __addc_cc(r[10], carry);

    carry3 = __addc(0, 0);
    r[10] = __add_cc(r[10], carry2);
    carry2 = __addc(0, 0) + carry3;


    k = r[5] * p_inv;
    __mad_lo_cc(k, p[0], r[5]);
    carry = __madc_hi_cc(k, p[0], 0);
    r[6] = __addc_cc(__madc_lo_cc(k, p[1], r[6]), carry);
    carry = __madc_hi_cc(k, p[1], 0);
    r[7] = __addc_cc(__madc_lo_cc(k, p[2], r[7]), carry);
    carry = __madc_hi_cc(k, p[2], 0);
    r[8] = __addc_cc(__madc_lo_cc(k, p[3], r[8]), carry);
    carry = __madc_hi_cc(k, p[3], 0);
    r[9] = __addc_cc(__madc_lo_cc(k, p[4], r[9]), carry);
    carry = __madc_hi_cc(k, p[4], 0);
    r[10] = __addc_cc(__madc_lo_cc(k, p[5], r[10]), carry);
    carry = __madc_hi_cc(k, p[5], 0);
    r[11] = __addc_cc(r[11], carry);

    // carry3 = __addc(0, 0);
    r[10] = __add_cc(r[11], carry2);
    // carry2 = __addc(0, 0) + carry3;

    reduce(ret, &r[6]);
}

__device__ void mul_mont_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p, limb_t p_inv) {
    limb_t r[12];
    
    r[0] = __mad_lo_cc(a[0], b[0], 0); //  mc_with_carry(a[0], b[0], &carry);
    limb_t carry = __madc_hi_cc(a[0], b[0], 0);
    r[1] = __madc_lo_cc(a[0], b[1], carry); // mc_with_carry(a[0], b[1], &carry);
    carry = __madc_hi_cc(a[0], b[1], 0);
    r[2] = __madc_lo_cc(a[1], b[2], carry); // mc_with_carry(a[0], b[2], &carry);
    carry = __madc_hi_cc(a[0], b[2], 0);
    r[3] = __madc_lo_cc(a[1], b[3], carry);
    carry = __madc_hi_cc(a[0], b[3], 0);
    r[3] = __madc_lo_cc(a[1], b[4], carry);
    carry = __madc_hi_cc(a[0], b[4], 0);
    r[3] = __madc_lo_cc(a[1], b[5], carry);
    r[6] = __madc_hi(a[0], b[5], 0);

    r[1] = __mad_lo_cc(a[1], b[0], r[1]); //mac_with_carry(r[1], a[1], b[0], &carry);
    carry = __madc_hi_cc(a[1], b[0], r[1]);
    r[2] = __addc_cc(__madc_lo_cc(a[1], b[1], r[2]), carry); //     r[2] = mac_with_carry(r[2], a[1], b[1], &carry);
    carry = __madc_hi_cc(a[1], b[1], r[2]);
    r[3] = __addc_cc(__madc_lo_cc(a[1], b[2], r[3]), carry);
    carry = __madc_hi_cc(a[1], b[2], r[3]);
    r[4] = __addc_cc(__madc_lo_cc(a[1], b[3], r[4]), carry);
    carry = __madc_hi_cc(a[1], b[3], r[4]);
    r[5] = __addc_cc(__madc_lo_cc(a[1], b[4], r[5]), carry);
    carry = __madc_hi_cc(a[1], b[4], r[5]);
    r[6] = __addc_cc(__madc_lo_cc(a[1], b[5], r[6]), carry);
    r[7] = __madc_hi(a[1], b[5], r[6]);

    r[2] = __mad_lo_cc(a[2], b[0], r[2]);
    carry = __madc_hi_cc(a[2], b[0], r[2]);
    r[3] = __addc_cc(__madc_lo_cc(a[2], b[1], r[3]), carry);
    carry = __madc_hi_cc(a[2], b[1], r[3]);
    r[4] = __addc_cc(__madc_lo_cc(a[2], b[2], r[4]), carry);
    carry = __madc_hi_cc(a[2], b[2], r[4]);
    r[5] = __addc_cc(__madc_lo_cc(a[2], b[3], r[5]), carry);
    carry = __madc_hi_cc(a[2], b[3], r[5]);
    r[6] = __addc_cc(__madc_lo_cc(a[2], b[4], r[6]), carry);
    carry = __madc_hi_cc(a[2], b[4], r[6]);
    r[7] = __addc_cc(__madc_lo_cc(a[2], b[5], r[7]), carry);
    r[8] = __madc_hi(a[2], b[5], r[7]);
    
    r[3] = __mad_lo_cc(a[3], b[0], r[3]);
    carry = __madc_hi_cc(a[3], b[0], r[3]);
    r[4] = __addc_cc(__madc_lo_cc(a[3], b[1], r[4]), carry);
    carry = __madc_hi_cc(a[3], b[1], r[4]);
    r[5] = __addc_cc(__madc_lo_cc(a[3], b[2], r[5]), carry);
    carry = __madc_hi_cc(a[3], b[2], r[5]);
    r[6] = __addc_cc(__madc_lo_cc(a[3], b[3], r[6]), carry);
    carry = __madc_hi_cc(a[3], b[3], r[6]);
    r[7] = __addc_cc(__madc_lo_cc(a[3], b[4], r[7]), carry);
    carry = __madc_hi_cc(a[3], b[4], r[7]);
    r[8] = __addc_cc(__madc_lo_cc(a[3], b[5], r[8]), carry);
    r[9] = __madc_hi(a[3], b[5], r[8]);
    
    r[4] = __mad_lo_cc(a[4], b[0], r[4]);
    carry = __madc_hi_cc(a[4], b[0], r[4]);
    r[5] = __addc_cc(__madc_lo_cc(a[4], b[1], r[5]), carry);
    carry = __madc_hi_cc(a[4], b[1], r[5]);
    r[6] = __addc_cc(__madc_lo_cc(a[4], b[2], r[6]), carry);
    carry = __madc_hi_cc(a[4], b[2], r[6]);
    r[7] = __addc_cc(__madc_lo_cc(a[4], b[3], r[7]), carry);
    carry = __madc_hi_cc(a[4], b[3], r[7]);
    r[8] = __addc_cc(__madc_lo_cc(a[4], b[4], r[8]), carry);
    carry = __madc_hi_cc(a[4], b[4], r[8]);
    r[9] = __addc_cc(__madc_lo_cc(a[4], b[5], r[9]), carry);
    r[10] = __madc_hi(a[4], b[5], r[9]);

    r[5] = __mad_lo_cc(a[5], b[0], r[5]);
    carry = __madc_hi_cc(a[5], b[0], r[5]);
    r[6] = __addc_cc(__madc_lo_cc(a[5], b[1], r[6]), carry);
    carry = __madc_hi_cc(a[5], b[1], r[6]);
    r[7] = __addc_cc(__madc_lo_cc(a[5], b[2], r[7]), carry);
    carry = __madc_hi_cc(a[5], b[2], r[7]);
    r[8] = __addc_cc(__madc_lo_cc(a[5], b[3], r[8]), carry);
    carry = __madc_hi_cc(a[5], b[3], r[8]);
    r[9] = __addc_cc(__madc_lo_cc(a[5], b[4], r[9]), carry);
    carry = __madc_hi_cc(a[5], b[4], r[9]);
    r[10] = __addc_cc(__madc_lo_cc(a[5], b[5], r[10]), carry);
    r[11] = __madc_hi(a[5], b[5], r[10]);

    mont_384(ret, r, p, p_inv);
}

__device__ void sqr_mont_384(blst_fp ret, const blst_fp a, const blst_fp p, limb_t p_inv) {
    limb_t r[12];
    r[1] = __mad_lo_cc(a[0], a[1], 0); // todo mul_low
    limb_t carry = __madc_hi_cc(a[0], a[1], 0);
    r[2] = __madc_lo_cc(a[0], a[2], carry);
    carry = __madc_hi_cc(a[0], a[2], 0);
    r[3] = __madc_lo_cc(a[0], a[3], carry);
    carry = __madc_hi_cc(a[0], a[3], 0);
    r[4] = __madc_lo_cc(a[0], a[4], carry);
    carry = __madc_hi_cc(a[0], a[4], 0);
    r[5] = __madc_lo_cc(a[0], a[5], carry);
    r[6] = __madc_hi(a[0], a[5], 0);

    r[3] = __mad_lo_cc(a[1], a[2], r[3]);
    carry = __madc_hi_cc(a[1], a[2], 0);
    r[4] = __addc_cc(__madc_lo_cc(a[1], a[3], r[4]), carry);
    carry = __madc_hi_cc(a[1], a[3], 0);
    r[5] = __addc_cc(__madc_lo_cc(a[1], a[4], r[5]), carry);
    carry = __madc_hi_cc(a[1], a[4], 0);
    r[6] = __addc_cc(__madc_lo_cc(a[1], a[5], r[6]), carry);
    r[7] = __madc_hi(a[1], a[5], 0);

    r[5] = __mad_lo_cc(a[2], a[3], r[4]);
    carry = __madc_hi_cc(a[2], a[3], 0);
    r[6] = __addc_cc(__madc_lo_cc(a[2], a[4], r[6]), carry);
    carry = __madc_hi_cc(a[2], a[4], 0);
    r[7] = __addc_cc(__madc_lo_cc(a[2], a[4], r[7]), carry);
    r[8] = __madc_hi(a[2], a[5], 0);

    r[7] = __mad_lo_cc(a[3], a[4], r[7]);
    carry = __madc_hi_cc(a[3], a[4], 0);
    r[8] = __addc_cc(__madc_lo_cc(a[3], a[5], r[8]), carry);
    r[9] = __madc_hi(a[3], a[5], 0);

    r[9] = __mad_lo_cc(a[4], a[5], r[9]);
    r[10] = __madc_hi(a[3], a[5], 0);

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

    r[0] = __mad_lo_cc(a[0], a[0], 0);
    carry = __madc_hi_cc(a[0], a[0], 0);
    r[1] = __addc_cc(r[1], carry);

    r[2] = __madc_lo_cc(a[1], a[1], r[2]);
    carry = __madc_hi_cc(a[1], a[1], 0);
    r[3] = __addc_cc(r[3], carry);

    r[4] = __madc_lo_cc(a[2], a[2], r[4]);
    carry = __madc_hi_cc(a[2], a[2], 0);
    r[5] = __addc_cc(r[5], carry);

    r[6] = __madc_lo_cc(a[3], a[3], r[6]);
    carry = __madc_hi_cc(a[3], a[3], 0);
    r[7] = __addc_cc(r[7], carry);

    r[8] = __madc_lo_cc(a[4], a[4], r[8]);
    carry = __madc_hi_cc(a[4], a[4], 0);
    r[9] = __addc_cc(r[9], carry);

    r[10] = __madc_lo_cc(a[5], a[5], r[10]);
    carry = __madc_hi_cc(a[5], a[5], 0);
    r[11] = __addc_cc(r[11], carry);

    mont_384(ret, r, p, p_inv);
}

__device__ void add_mod_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p) {
    ret[0] = __add_cc(a[0], b[0]);
    ret[1] = __addc_cc(a[1], b[1]);
    ret[2] = __addc_cc(a[2], b[2]);
    ret[3] = __addc_cc(a[3], b[3]);
    ret[4] = __addc_cc(a[4], b[4]);
    ret[5] = __addc(a[5], b[5]);

    reduce(ret, p);
    // return cf != 0?
}

__device__ void sub_mod_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p) {
    sub_mod_384_unchecked(ret, a, b);
    reduce(ret, p);
    // return cf != 0?
}

__device__ static inline void _lshift_384(blst_fp ret, const blst_fp value) {
    ret[0] = __add_cc(value[0], value[0]);
    ret[1] = __addc_cc(value[1], value[1]);
    ret[2] = __addc_cc(value[2], value[2]);
    ret[3] = __addc_cc(value[3], value[3]);
    ret[4] = __addc_cc(value[4], value[4]);
    ret[5] = __addc(value[5], value[5]);
}

__device__ void mul_by_3_mod_384(blst_fp ret, const blst_fp a, const blst_fp p) {
    _lshift_384(ret, a);
    add_mod_384(ret, ret, a, p);
}

__device__ void mul_by_8_mod_384(blst_fp ret, const blst_fp a, const blst_fp p) {
    _lshift_384(ret, a);
    _lshift_384(ret, a);
    _lshift_384(ret, a);
    reduce(ret, p);
}

__device__ void cneg_mod_384(blst_fp ret, const blst_fp a, bool flag, const blst_fp p) {
    // just let the compiler cmov
    if (flag) {
        sub_mod_384(ret, p, a, p);
    } else {
        memcpy(ret, a, 6 * sizeof(limb_t));
    }
}
