#ifndef __BLS12_377_OPS_H__
#define __BLS12_377_OPS_H__

#include "asm_cuda.h"
#include "types.h"

__device__ static inline void blst_fp_add(blst_fp ret, const blst_fp a, const blst_fp b)
{   add_mod_384(ret, a, b, BLS12_377_P);   }

__device__ static inline void blst_fp_add_unsafe(blst_fp ret, const blst_fp a, const blst_fp b)
{   add_mod_384_unsafe(ret, a, b);   }

__device__ static inline void blst_fp_sub(blst_fp ret, const blst_fp a, const blst_fp b)
{   sub_mod_384(ret, a, b, BLS12_377_P);   }

__device__ static inline void blst_fp_sub_unsafe(blst_fp ret, const blst_fp a, const blst_fp b)
{   sub_mod_384_unsafe(ret, a, b);   }

__device__ static inline void blst_fp_cneg(blst_fp ret, const blst_fp a, bool flag)
{   cneg_mod_384(ret, a, flag, BLS12_377_P);   }

__device__ static inline void blst_fp_mul(blst_fp ret, const blst_fp a, const blst_fp b)
{   mul_mont_384(ret, a, b, BLS12_377_P, BLS12_377_p0);   }

__device__ static inline void blst_fp_sqr(blst_fp ret, const blst_fp a)
{   sqr_mont_384(ret, a, BLS12_377_P, BLS12_377_p0);   }

__device__ void blst_fp_inverse(blst_fp out, const blst_fp in);

__device__ void blst_p1_add_affine_to_projective(blst_p1 *out, const blst_p1 *p1, const blst_p1_affine *p2);
__device__ void blst_p1_add_projective_to_projective(blst_p1 *out, const blst_p1 *p1, const blst_p1 *p2);
__device__ void blst_p1_projective_into_affine(blst_p1_affine* out, const blst_p1* in);
__device__ void blst_p1_add_affines_into_projective(blst_p1* out, const blst_p1_affine* p1, const blst_p1_affine* p2);
__device__ void blst_p1_add_affine_to_affine(blst_p1_affine* out, const blst_p1_affine* p1, const blst_p1_affine* p2);
__device__ void blst_p1_double(blst_p1* out, const blst_p1* in);
#endif /* __BLS12_377_OPS_H__ */
