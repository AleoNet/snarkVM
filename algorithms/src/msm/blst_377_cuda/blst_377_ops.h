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

typedef unsigned long long limb_t;
# define LIMB_T_BITS    64

/*
 * Why isn't LIMB_T_BITS defined as 8*sizeof(limb_t)? Because pre-processor
 * knows nothing about sizeof(anything)...
 */
# define TO_LIMB_T(limb64)     limb64

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

typedef limb_t blst_scalar[NLIMBS(256)];
typedef limb_t blst_fr[NLIMBS(256)];
typedef limb_t blst_fp[NLIMBS(384)];
typedef limb_t vec768[NLIMBS(768)];

typedef struct { blst_fp X, Y; } blst_p1_affine;
typedef struct { blst_fp X, Y, Z; } blst_p1;
typedef struct { blst_fp X, Y, ZZ, ZZZ; } blst_p1_ext;

#define ONE_MONT_P TO_LIMB_T(0x02cdffffffffff68), \
                 TO_LIMB_T(0x51409f837fffffb1), \
                 TO_LIMB_T(0x9f7db3a98a7d3ff2), \
                 TO_LIMB_T(0x7b4e97b76e7c6305), \
                 TO_LIMB_T(0x4cf495bf803c84e8), \
                 TO_LIMB_T(0x008d6661e2fdf49a)

__device__ static const blst_fp BLS12_377_P = {
  TO_LIMB_T(0x8508c00000000001), TO_LIMB_T(0x170b5d4430000000),
  TO_LIMB_T(0x1ef3622fba094800), TO_LIMB_T(0x1a22d9f300f5138f),
  TO_LIMB_T(0xc63b05c06ca1493b), TO_LIMB_T(0x1ae3a4617c510ea)
};
__device__ static const blst_fp BLS12_377_ONE { ONE_MONT_P };
__device__ static const limb_t BLS12_377_p0 = (limb_t)0x8508bfffffffffff;
extern const blst_p1 BLS12_377_G1_MONT;
extern const blst_p1_affine BLS12_377_G1_MONT_AFFINE;
extern const blst_scalar BLS12_377_r;
extern const blst_scalar BLS12_377_rRR;
static const limb_t r0 = (limb_t)0x0a117fffffffffff;

__device__ void add_mod_384(blst_fp ret, const blst_fp a, const blst_fp b,
                 const blst_fp p);
__device__ void sub_mod_384(blst_fp ret, const blst_fp a, const blst_fp b,
                 const blst_fp p);
__device__ void mul_by_3_mod_384(blst_fp ret, const blst_fp a, const blst_fp p);
__device__ void mul_by_8_mod_384(blst_fp ret, const blst_fp a, const blst_fp p);
__device__ void cneg_mod_384(blst_fp ret, const blst_fp a, bool flag, const blst_fp p);

__device__ void mul_mont_384(blst_fp ret, const blst_fp a, const blst_fp b,
                  const blst_fp p, limb_t n0);
__device__ void sqr_mont_384(blst_fp ret, const blst_fp a, const blst_fp p, limb_t n0);

__device__ static inline void blst_fp_add(blst_fp ret, const blst_fp a, const blst_fp b)
{   add_mod_384(ret, a, b, BLS12_377_P);   }

__device__ static inline void blst_fp_sub(blst_fp ret, const blst_fp a, const blst_fp b)
{   sub_mod_384(ret, a, b, BLS12_377_P);   }

__device__ static inline void blst_fp_mul_by_3(blst_fp ret, const blst_fp a)
{   mul_by_3_mod_384(ret, a, BLS12_377_P);   }

__device__ static inline void blst_fp_mul_by_8(blst_fp ret, const blst_fp a)
{   mul_by_8_mod_384(ret, a, BLS12_377_P);   }

__device__ static inline void blst_fp_cneg(blst_fp ret, const blst_fp a, bool flag)
{   cneg_mod_384(ret, a, flag, BLS12_377_P);   }

__device__ static inline void blst_fp_mul(blst_fp ret, const blst_fp a, const blst_fp b)
{   mul_mont_384(ret, a, b, BLS12_377_P, BLS12_377_p0);   }

__device__ static inline void blst_fp_sqr(blst_fp ret, const blst_fp a)
{   sqr_mont_384(ret, a, BLS12_377_P, BLS12_377_p0);   }


__device__ void blst_p1_add_or_double(blst_p1 *out, const blst_p1 *p1, const blst_p1 *p2);
__device__ void blst_p1_add_or_double_affine(blst_p1 *out, const blst_p1 *p1,
                                                const blst_p1_affine *p2);
__device__ void blst_p1_double(blst_p1 *out, const blst_p1 *p1);
__device__ bool blst_p1_is_inf(const blst_p1 *a);

__device__ void blst_p1_ext_add_or_double_affine(blst_p1_ext *out, const blst_p1_ext *p1,
                                      const blst_p1_affine *p2);
__device__ void blst_p1_ext_double_affine(blst_p1_ext *out, const blst_p1_affine *p1);
__device__ void blst_p1_from_extended_no_check(blst_p1 *out, const blst_p1_ext *in);
__device__ bool blst_p1_ext_is_inf(const blst_p1_ext *a);

#ifdef __cplusplus
}
#endif
#endif /* __BLS12_377_OPS_H__ */
