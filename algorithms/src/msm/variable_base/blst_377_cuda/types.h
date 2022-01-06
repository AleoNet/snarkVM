#pragma once

#ifdef __SIZE_TYPE__
typedef __SIZE_TYPE__ size_t;
#else
#include <stddef.h>
#endif

#include <stdint.h>

typedef unsigned long long limb_t;
# define LIMB_T_BITS    64

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
__device__ static const blst_fp BLS12_377_ZERO { 0 };
__device__ static const blst_fp BLS12_377_ONE { ONE_MONT_P };
__device__ static const blst_fp BLS12_377_R2 {
  0xb786686c9400cd22,
  0x329fcaab00431b1,
  0x22a5f11162d6b46d,
  0xbfdf7d03827dc3ac,
  0x837e92f041790bf9,
  0x6dfccb1e914b88,
};
__device__ static const limb_t BLS12_377_p0 = (limb_t)0x8508bfffffffffff;
__device__ extern const blst_p1 BLS12_377_ZERO_PROJECTIVE;
__device__ extern const blst_p1_affine BLS12_377_ZERO_AFFINE;
__device__ extern const blst_scalar BLS12_377_R;

