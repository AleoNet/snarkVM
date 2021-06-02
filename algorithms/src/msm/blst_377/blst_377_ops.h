#ifndef __BLS12_377_OPS_H__
#define __BLS12_377_OPS_H__

#ifdef __SIZE_TYPE__
typedef __SIZE_TYPE__ size_t;
#else
#include <stddef.h>
#endif

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#elif defined(__BLST_CGO__)
typedef _Bool bool; /* it's assumed that cgo calls modern enough compiler */
#elif defined(__STDC_VERSION__) && __STDC_VERSION__>=199901
# define bool _Bool
#else
# define bool int
#endif

#ifdef __UINTPTR_TYPE__
typedef __UINTPTR_TYPE__ uptr_t;
#else
typedef const void *uptr_t;
#endif

#if defined(__x86_64__) || defined(__aarch64__)
/* These are available even in ILP32 flavours, but even then they are
 * capable of performing 64-bit operations as efficiently as in *P64. */
typedef unsigned long long limb_t;
# define LIMB_T_BITS    64

#elif defined(_WIN64)   /* Win64 is P64 */
typedef unsigned __int64 limb_t;
# define LIMB_T_BITS    64

#elif defined(__BLST_NO_ASM__) || defined(__wasm64__)
typedef unsigned int limb_t;
# define LIMB_T_BITS    32
# ifndef __BLST_NO_ASM__
#  define __BLST_NO_ASM__
# endif

#else                   /* 32 bits on 32-bit platforms, 64 - on 64-bit */
typedef unsigned long limb_t;
#  ifdef _LP64
#   define LIMB_T_BITS   64
#  else
#   define LIMB_T_BITS   32
#   define __BLST_NO_ASM__
#  endif
#endif

/*
 * Why isn't LIMB_T_BITS defined as 8*sizeof(limb_t)? Because pre-processor
 * knows nothing about sizeof(anything)...
 */
#if LIMB_T_BITS == 64
# define TO_LIMB_T(limb64)     limb64
#else
# define TO_LIMB_T(limb64)     (limb_t)limb64,(limb_t)(limb64>>32)
#endif

#define NLIMBS(bits)   (bits/LIMB_T_BITS)

#if !defined(restrict)
# if !defined(__STDC_VERSION__) || __STDC_VERSION__<199901
#  if defined(__GNUC__) && __GNUC__>=2
#   define restrict __restrict__
#  elif defined(_MSC_VER)
#   define restrict __restrict
#  else
#   define restrict
#  endif
# endif
#endif


typedef unsigned char byte;
#define TO_BYTES(limb64)    (byte)limb64,(byte)(limb64>>8),\
                            (byte)(limb64>>16),(byte)(limb64>>24),\
                            (byte)(limb64>>32),(byte)(limb64>>40),\
                            (byte)(limb64>>48),(byte)(limb64>>56)

typedef limb_t blst_scalar[NLIMBS(256)];
typedef limb_t blst_fr[NLIMBS(256)];
typedef limb_t blst_fp[NLIMBS(384)];
typedef limb_t vec768[NLIMBS(768)];

typedef struct { blst_fp X, Y; } blst_p1_affine;
typedef struct { blst_fp X, Y, Z; } blst_p1;
typedef struct { blst_fp X, Y, ZZ, ZZZ; } blst_p1_ext;

extern const blst_fp BLS12_377_P;
extern const blst_fp BLS12_377_ONE;
extern const limb_t BLS12_377_p0;
extern const blst_p1 BLS12_377_G1_MONT;
extern const blst_p1_affine BLS12_377_G1_MONT_AFFINE;
extern const blst_scalar BLS12_377_r;
extern const blst_scalar BLS12_377_rRR;
static const limb_t r0 = (limb_t)0x0a117fffffffffff;

void add_mod_384(blst_fp ret, const blst_fp a, const blst_fp b,
                 const blst_fp p);
void sub_mod_384(blst_fp ret, const blst_fp a, const blst_fp b,
                 const blst_fp p);
void mul_by_3_mod_384(blst_fp ret, const blst_fp a, const blst_fp p);
void mul_by_8_mod_384(blst_fp ret, const blst_fp a, const blst_fp p);
void cneg_mod_384(blst_fp ret, const blst_fp a, bool flag, const blst_fp p);

#if defined(__ADX__) /* e.g. -march=broadwell */ && !defined(__BLST_PORTABLE__)
# define mul_mont_384 mulx_mont_384
# define sqr_mont_384 sqrx_mont_384
#endif

void mul_mont_384(blst_fp ret, const blst_fp a, const blst_fp b,
                  const blst_fp p, limb_t n0);
void sqr_mont_384(blst_fp ret, const blst_fp a, const blst_fp p, limb_t n0);

static inline void blst_fp_add(blst_fp ret, const blst_fp a, const blst_fp b)
{   add_mod_384(ret, a, b, BLS12_377_P);   }

static inline void blst_fp_sub(blst_fp ret, const blst_fp a, const blst_fp b)
{   sub_mod_384(ret, a, b, BLS12_377_P);   }

static inline void blst_fp_mul_by_3(blst_fp ret, const blst_fp a)
{   mul_by_3_mod_384(ret, a, BLS12_377_P);   }

static inline void blst_fp_mul_by_8(blst_fp ret, const blst_fp a)
{   mul_by_8_mod_384(ret, a, BLS12_377_P);   }

static inline void blst_fp_cneg(blst_fp ret, const blst_fp a, bool flag)
{   cneg_mod_384(ret, a, flag, BLS12_377_P);   }

static inline void blst_fp_mul(blst_fp ret, const blst_fp a, const blst_fp b)
{   mul_mont_384(ret, a, b, BLS12_377_P, BLS12_377_p0);   }

static inline void blst_fp_sqr(blst_fp ret, const blst_fp a)
{   sqr_mont_384(ret, a, BLS12_377_P, BLS12_377_p0);   }


void blst_p1_add_or_double(blst_p1 *out, const blst_p1 *p1, const blst_p1 *p2);
void blst_p1_add_or_double_affine(blst_p1 *out, const blst_p1 *p1,
                                                const blst_p1_affine *p2);
void blst_p1_double(blst_p1 *out, const blst_p1 *p1);
bool blst_p1_is_inf(const blst_p1 *a);

void blst_p1_ext_add_or_double_affine(blst_p1_ext *out, const blst_p1_ext *p1,
                                      const blst_p1_affine *p2);
void blst_p1_ext_double_affine(blst_p1_ext *out, const blst_p1_affine *p1);
void blst_p1_from_extended_no_check(blst_p1 *out, const blst_p1_ext *in);
bool blst_p1_ext_is_inf(const blst_p1_ext *a);

#ifdef __cplusplus
}
#endif
#endif /* __BLS12_377_OPS_H__ */
