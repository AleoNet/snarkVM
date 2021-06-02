#include "blst_377_ops.h"
#include <immintrin.h>
#include <string.h>

static inline limb_t mac_with_carry(limb_t a, limb_t b, limb_t c, limb_t* carry) {
    uint8_t a_carry = _addcarryx_u64(0, *carry, a, &a);
    limb_t hi;
    limb_t lo = _mulx_u64(b, c, &hi);
    uint8_t a_low_carry = _addcarryx_u64(0, a, lo, &lo);
    *carry = hi + a_low_carry + a_carry;
    return lo;
}

static inline limb_t mc_with_carry(limb_t b, limb_t c, limb_t* carry) {
    limb_t hi;
    limb_t lo = _mulx_u64(b, c, &hi);
    uint8_t a_low_carry = _addcarryx_u64(0, *carry, lo, &lo);
    *carry = hi + a_low_carry;
    return lo;
}

static inline limb_t adc(limb_t a, limb_t b, limb_t* carry) {
    uint8_t a_carry = _addcarryx_u64(0, a, b, &a);
    uint8_t b_carry = _addcarryx_u64(0, a, *carry, &a);
    
    *carry = a_carry + b_carry;
    
    return a;
}

static inline limb_t ac(limb_t a, limb_t* carry) {
    *carry = _addcarryx_u64(0, a, *carry, &a);
    
    return a;
}

static inline int is_ge_384(const blst_fp left, const blst_fp right) {
    for (int i = 5; i >= 0; --i) {
        if (left[i] < right[i]) {
            return 0;
        } else if (right[i] > left[i]) {
            return 1;
        }
    }
    return 1;
}

static inline void sub_mod_384_unchecked(blst_fp ret, const blst_fp a, const blst_fp b) {
    uint8_t cf = 0;
    cf = _subborrow_u64(cf, a[0], b[0], &ret[0]);
    cf = _subborrow_u64(cf, a[1], b[1], &ret[1]);
    cf = _subborrow_u64(cf, a[2], b[2], &ret[2]);
    cf = _subborrow_u64(cf, a[3], b[3], &ret[3]);
    cf = _subborrow_u64(cf, a[4], b[4], &ret[4]);
    _subborrow_u64(cf, a[5], b[5], &ret[5]);
    // return cf != 0?
}

static inline void reduce(blst_fp x, const blst_fp p) {
    blst_fp x_sub;
    sub_mod_384_unchecked(x_sub, x, p);
    if (is_ge_384(x, p)) {
        memcpy(x, x_sub, sizeof(blst_fp));
    }
}

// The Montgomery reduction here is based on Algorithm 14.32 in
// Handbook of Applied Cryptography
// <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.
static inline void mont_384(blst_fp ret, limb_t r[12], const blst_fp p, const limb_t p_inv) {
    limb_t k = r[0] * p_inv;
    limb_t carry = 0;
    mac_with_carry(r[0], k, p[0], &carry);
    r[1] = mac_with_carry(r[1], k, p[1], &carry);
    r[2] = mac_with_carry(r[2], k, p[2], &carry);
    r[3] = mac_with_carry(r[3], k, p[3], &carry);
    r[4] = mac_with_carry(r[4], k, p[4], &carry);
    r[5] = mac_with_carry(r[5], k, p[5], &carry);
    r[6] = adc(r[6], 0, &carry);

    limb_t carry2 = carry;
    k = r[1] * p_inv;
    carry = 0;
    mac_with_carry(r[1], k, p[0], &carry);
    r[2] = mac_with_carry(r[2], k, p[1], &carry);
    r[3] = mac_with_carry(r[3], k, p[2], &carry);
    r[4] = mac_with_carry(r[4], k, p[3], &carry);
    r[5] = mac_with_carry(r[5], k, p[4], &carry);
    r[6] = mac_with_carry(r[6], k, p[5], &carry);
    r[7] = adc(r[7], carry2, &carry);

    carry2 = carry;
    k = r[2] * p_inv;
    carry = 0;
    mac_with_carry(r[2], k, p[0], &carry);
    r[3] = mac_with_carry(r[3], k, p[1], &carry);
    r[4] = mac_with_carry(r[4], k, p[2], &carry);
    r[5] = mac_with_carry(r[5], k, p[3], &carry);
    r[6] = mac_with_carry(r[6], k, p[4], &carry);
    r[7] = mac_with_carry(r[7], k, p[5], &carry);
    r[8] = adc(r[8], carry2, &carry);

    carry2 = carry;
    k = r[3] * p_inv;
    carry = 0;
    mac_with_carry(r[3], k, p[0], &carry);
    r[4] = mac_with_carry(r[4], k, p[1], &carry);
    r[5] = mac_with_carry(r[5], k, p[2], &carry);
    r[6] = mac_with_carry(r[6], k, p[3], &carry);
    r[7] = mac_with_carry(r[7], k, p[4], &carry);
    r[8] = mac_with_carry(r[8], k, p[5], &carry);
    r[9] = adc(r[9], carry2, &carry);

    carry2 = carry;
    k = r[4] * p_inv;
    carry = 0;
    mac_with_carry(r[4], k, p[0], &carry);
    r[5] = mac_with_carry(r[5], k, p[1], &carry);
    r[6] = mac_with_carry(r[6], k, p[2], &carry);
    r[7] = mac_with_carry(r[7], k, p[3], &carry);
    r[8] = mac_with_carry(r[8], k, p[4], &carry);
    r[9] = mac_with_carry(r[9], k, p[5], &carry);
    r[10] = adc(r[10], carry2, &carry);

    carry2 = carry;
    k = r[5] * p_inv;
    carry = 0;
    mac_with_carry(r[5], k, p[0], &carry);
    r[6] = mac_with_carry(r[6], k, p[1], &carry);
    r[7] = mac_with_carry(r[7], k, p[2], &carry);
    r[8] = mac_with_carry(r[8], k, p[3], &carry);
    r[9] = mac_with_carry(r[9], k, p[4], &carry);
    r[10] = mac_with_carry(r[10], k, p[5], &carry);
    r[11] = adc(r[11], carry2, &carry);
    
    reduce(ret, &r[6]);
}

void mul_mont_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p, limb_t p_inv) {
    limb_t r[12];
    limb_t carry = 0;
    r[0] = mc_with_carry(a[0], b[0], &carry);
    r[1] = mc_with_carry(a[0], b[1], &carry);
    r[2] = mc_with_carry(a[0], b[2], &carry);
    r[3] = mc_with_carry(a[0], b[3], &carry);
    r[4] = mc_with_carry(a[0], b[4], &carry);
    r[5] = mc_with_carry(a[0], b[5], &carry);
    r[6] = carry;

    carry = 0;
    r[1] = mac_with_carry(r[1], a[1], b[0], &carry);
    r[2] = mac_with_carry(r[2], a[1], b[1], &carry);
    r[3] = mac_with_carry(r[3], a[1], b[2], &carry);
    r[4] = mac_with_carry(r[4], a[1], b[3], &carry);
    r[5] = mac_with_carry(r[5], a[1], b[4], &carry);
    r[6] = mac_with_carry(r[6], a[1], b[5], &carry);
    r[7] = carry;

    carry = 0;
    r[2] = mac_with_carry(r[2], a[2], b[0], &carry);
    r[3] = mac_with_carry(r[3], a[2], b[1], &carry);
    r[4] = mac_with_carry(r[4], a[2], b[2], &carry);
    r[5] = mac_with_carry(r[5], a[2], b[3], &carry);
    r[6] = mac_with_carry(r[6], a[2], b[4], &carry);
    r[7] = mac_with_carry(r[7], a[2], b[5], &carry);
    r[8] = carry;
    
    carry = 0;
    r[3] = mac_with_carry(r[3], a[3], b[0], &carry);
    r[4] = mac_with_carry(r[4], a[3], b[1], &carry);
    r[5] = mac_with_carry(r[5], a[3], b[2], &carry);
    r[6] = mac_with_carry(r[6], a[3], b[3], &carry);
    r[7] = mac_with_carry(r[7], a[3], b[4], &carry);
    r[8] = mac_with_carry(r[8], a[3], b[5], &carry);
    r[9] = carry;
    
    carry = 0;
    r[4] = mac_with_carry(r[4], a[4], b[0], &carry);
    r[5] = mac_with_carry(r[5], a[4], b[1], &carry);
    r[6] = mac_with_carry(r[6], a[4], b[2], &carry);
    r[7] = mac_with_carry(r[7], a[4], b[3], &carry);
    r[8] = mac_with_carry(r[8], a[4], b[4], &carry);
    r[9] = mac_with_carry(r[9], a[4], b[5], &carry);
    r[10] = carry;

    carry = 0;
    r[5] = mac_with_carry(r[5], a[5], b[0], &carry);
    r[6] = mac_with_carry(r[6], a[5], b[1], &carry);
    r[7] = mac_with_carry(r[7], a[5], b[2], &carry);
    r[8] = mac_with_carry(r[8], a[5], b[3], &carry);
    r[9] = mac_with_carry(r[9], a[5], b[4], &carry);
    r[10] = mac_with_carry(r[10], a[5], b[5], &carry);
    r[11] = carry;
    mont_384(ret, r, p, p_inv);
}

void sqr_mont_384(blst_fp ret, const blst_fp a, const blst_fp p, limb_t p_inv) {
    limb_t r[12];
    limb_t carry = 0;
    r[1] = mc_with_carry(a[0], a[1], &carry);
    r[2] = mc_with_carry(a[0], a[2], &carry);
    r[3] = mc_with_carry(a[0], a[3], &carry);
    r[4] = mc_with_carry(a[0], a[4], &carry);
    r[5] = mc_with_carry(a[0], a[5], &carry);
    r[6] = carry;

    carry = 0;
    r[3] = mac_with_carry(r[3], a[1], a[2], &carry);
    r[4] = mac_with_carry(r[4], a[1], a[3], &carry);
    r[5] = mac_with_carry(r[5], a[1], a[4], &carry);
    r[6] = mac_with_carry(r[6], a[1], a[5], &carry);
    r[7] = carry;

    carry = 0;
    r[5] = mac_with_carry(r[5], a[2], a[3], &carry);
    r[6] = mac_with_carry(r[6], a[2], a[4], &carry);
    r[7] = mac_with_carry(r[7], a[2], a[5], &carry);
    r[8] = carry;
    
    carry = 0;
    r[7] = mac_with_carry(r[7], a[3], a[4], &carry);
    r[8] = mac_with_carry(r[8], a[3], a[5], &carry);
    r[9] = carry;
    
    carry = 0;
    r[9] = mac_with_carry(r[9], a[4], a[5], &carry);
    r[10] = carry;

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

    carry = 0;
    r[0] = mc_with_carry(a[0], a[0], &carry);
    r[1] = ac(r[1], &carry);
    r[2] = mac_with_carry(r[2], a[1], a[1], &carry);
    r[3] = ac(r[1], &carry);
    r[4] = mac_with_carry(r[4], a[2], a[2], &carry);
    r[5] = ac(r[5], &carry);
    r[6] = mac_with_carry(r[6], a[3], a[3], &carry);
    r[7] = ac(r[7], &carry);
    r[8] = mac_with_carry(r[8], a[4], a[4], &carry);
    r[9] = ac(r[9], &carry);
    r[10] = mac_with_carry(r[10], a[5], a[5], &carry);
    r[11] = ac(r[11], &carry);

    mont_384(ret, r, p, p_inv);
}

void add_mod_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p) {
    uint8_t cf = 0;
    cf = _addcarryx_u64(cf, a[0], b[0], &ret[0]);
    cf = _addcarryx_u64(cf, a[1], b[1], &ret[1]);
    cf = _addcarryx_u64(cf, a[2], b[2], &ret[2]);
    cf = _addcarryx_u64(cf, a[3], b[3], &ret[3]);
    cf = _addcarryx_u64(cf, a[4], b[4], &ret[4]);
    cf = _addcarryx_u64(cf, a[5], b[5], &ret[5]);
    reduce(ret, p);
    // return cf != 0?
}

void sub_mod_384(blst_fp ret, const blst_fp a, const blst_fp b, const blst_fp p) {
    uint8_t cf = 0;
    cf = _subborrow_u64(cf, a[0], b[0], &ret[0]);
    cf = _subborrow_u64(cf, a[1], b[1], &ret[1]);
    cf = _subborrow_u64(cf, a[2], b[2], &ret[2]);
    cf = _subborrow_u64(cf, a[3], b[3], &ret[3]);
    cf = _subborrow_u64(cf, a[4], b[4], &ret[4]);
    cf = _subborrow_u64(cf, a[5], b[5], &ret[5]);
    reduce(ret, p);
    // return cf != 0?
}

static inline void _lshift_384(blst_fp ret, const blst_fp value) {
    uint8_t cf = 0;
    cf = _addcarryx_u64(cf, value[0], value[0], &ret[0]);
    cf = _addcarryx_u64(cf, value[1], value[1], &ret[1]);
    cf = _addcarryx_u64(cf, value[2], value[2], &ret[2]);
    cf = _addcarryx_u64(cf, value[3], value[3], &ret[3]);
    cf = _addcarryx_u64(cf, value[4], value[4], &ret[4]);
    _addcarryx_u64(cf, value[5], value[5], &ret[5]);
}

void mul_by_3_mod_384(blst_fp ret, const blst_fp a, const blst_fp p) {
    _lshift_384(ret, a);
    add_mod_384(ret, ret, a, p);
}

void mul_by_8_mod_384(blst_fp ret, const blst_fp a, const blst_fp p) {
    _lshift_384(ret, a);
    _lshift_384(ret, a);
    _lshift_384(ret, a);
    reduce(ret, p);
}

void cneg_mod_384(blst_fp ret, const blst_fp a, bool flag, const blst_fp p) {
    // just let the compiler cmov
    if (flag) {
        sub_mod_384(ret, p, a, p);
    } else {
        memcpy(ret, a, 6 * sizeof(limb_t));
    }
}
