#include "blst_377_ops.h"

__device__ const blst_p1 BLS12_377_ZERO_PROJECTIVE = {
  {0},
  {ONE_MONT_P},
  {0}
};

__device__ const blst_p1_affine BLS12_377_ZERO_AFFINE = {
  {0},
  {ONE_MONT_P}
};

const blst_scalar BLS12_377_r = {
  TO_LIMB_T(0x0a11800000000001), TO_LIMB_T(0x59aa76fed0000001),
  TO_LIMB_T(0x60b44d1e5c37b001), TO_LIMB_T(0x12ab655e9a2ca556)
};

__device__ static inline void vec_select(void *ret, const void *a, const void *b,
                            size_t num, bool sel_a)
{
  limb_t bi, *rp = (limb_t *)ret;
  const limb_t *ap = (const limb_t *)a;
  const limb_t *bp = (const limb_t *)b;
  limb_t xorm, mask = (limb_t)0 - sel_a;
  size_t i;

  num /= sizeof(limb_t);

  for (i = 0; i < num; i++) {
    xorm = (ap[i] ^ (bi = bp[i])) & mask;
    rp[i] = bi ^ xorm;
  }
}

__device__ static inline bool is_zero(limb_t l)
{   return (~l & (l - 1)) >> (LIMB_T_BITS - 1);   }

__device__ static inline bool vec_is_zero(const void *a, size_t num)
{
  const limb_t *ap = (const limb_t *)a;
  limb_t acc;
  size_t i;

  num /= sizeof(limb_t);

  for (acc = 0, i = 0; i < num; i++)
    acc |= ap[i];

  return is_zero(acc);
}

__device__ static inline void vec_copy(void *restrict ret, const void *a, size_t num)
{
  limb_t *rp = (limb_t *)ret;
  const limb_t *ap = (const limb_t *)a;
  size_t i;

  num /= sizeof(limb_t);

  for (i = 0; i < num; i++)
    rp[i] = ap[i];
}

/*
 * Addition that can handle doubling [as well as points at infinity,
 * which are encoded as Z==0] in constant time. It naturally comes at
 * cost, but this subroutine should be called only when independent
 * points are processed, which is considered reasonable compromise.
 * For example, ptype##s_mult_w5 calls it, but since *major* gain is
 * result of pure doublings being effectively divided by amount of
 * points, slightly slower addition can be tolerated. But what is the
 * additional cost more specifically? Best addition result is 11M+5S,
 * while this routine takes 13M+5S (+1M+1S if a4!=0), as per
 *
 * -------------+-------------
 * addition     | doubling
 * -------------+-------------
 * U1 = X1*Z2^2 | U1 = X1
 * U2 = X2*Z1^2 |
 * S1 = Y1*Z2^3 | S1 = Y1
 * S2 = Y2*Z1^3 |
 * zz = Z1*Z2   | zz = Z1
 * H = U2-U1    | H' = 2*Y1
 * R = S2-S1    | R' = 3*X1^2[+a*Z1^4]
 * sx = U1+U2   | sx = X1+X1
 * -------------+-------------
 * H!=0 || R!=0 | H==0 && R==0
 *
 *      X3 = R^2-H^2*sx
 *      Y3 = R*(H^2*U1-X3)-H^3*S1
 *      Z3 = H*zz
 *
 * As for R!=0 condition in context of H==0, a.k.a. P-P. The result is
 * infinity by virtue of Z3 = (U2-U1)*zz = H*zz = 0*zz == 0.
 */
__device__ void blst_p1_add_or_double(blst_p1 *out, const blst_p1 *p1,
                                         const blst_p1 *p2) {
  blst_p1 p3; /* starts as (U1, S1, zz) from addition side */
  struct { blst_fp H, R, sx; } add, dbl; 
  bool p1inf, p2inf, is_dbl; 

  p2inf = vec_is_zero(p2->Z, sizeof(p2->Z)); 
  if (p2inf) {
    vec_copy(out, p1, sizeof(blst_p1));
    return;
  }
  p1inf = vec_is_zero(p1->Z, sizeof(p1->Z)); 
  if (p1inf) {
    vec_copy(out, p2, sizeof(blst_p1));
    return;
  }

  blst_fp_add(dbl.sx, p1->X, p1->X);  /* sx = X1+X1 */
  blst_fp_sqr(dbl.R, p1->X);          /* X1^2 */
  blst_fp_mul_by_3(dbl.R, dbl.R);     /* R = 3*X1^2 */
  blst_fp_add(dbl.H, p1->Y, p1->Y);   /* H = 2*Y1 */

  blst_fp_sqr(p3.X, p2->Z);           /* Z2^2 */
  blst_fp_mul(p3.Z, p1->Z, p2->Z);    /* Z1*Z2 */
  blst_fp_sqr(add.H, p1->Z);          /* Z1^2 */

  blst_fp_mul(p3.Y, p1->Y, p2->Z);    
  blst_fp_mul(p3.Y, p3.Y, p3.X);      /* S1 = Y1*Z2^3 */
  blst_fp_mul(add.R, p2->Y, p1->Z);   
  blst_fp_mul(add.R, add.R, add.H);   /* S2 = Y2*Z1^3 */
  blst_fp_sub(add.R, add.R, p3.Y);    /* R = S2-S1 */

  blst_fp_mul(p3.X, p3.X, p1->X);     /* U1 = X1*Z2^2 */
  blst_fp_mul(add.H, add.H, p2->X);   /* U2 = X2*Z1^2 */

  blst_fp_add(add.sx, add.H, p3.X);   /* sx = U1+U2 */
  blst_fp_sub(add.H, add.H, p3.X);    /* H = U2-U1 */

  /* make the choice between addition and doubling */
  is_dbl = vec_is_zero(add.H, 2*sizeof(add.H));      
  vec_select(&p3, p1, &p3, sizeof(p3), is_dbl);      
  vec_select(&add, &dbl, &add, sizeof(add), is_dbl); 
  /* |p3| and |add| hold all inputs now, |p3| will hold output */

  blst_fp_mul(p3.Z, p3.Z, add.H);     /* Z3 = H*Z1*Z2 */

  blst_fp_sqr(dbl.H, add.H);          /* H^2 */
  blst_fp_mul(dbl.R, dbl.H, add.H);   /* H^3 */
  blst_fp_mul(dbl.R, dbl.R, p3.Y);    /* H^3*S1 */
  blst_fp_mul(p3.Y, dbl.H, p3.X);     /* H^2*U1 */

  blst_fp_mul(dbl.H, dbl.H, add.sx);  /* H^2*sx */
  blst_fp_sqr(p3.X, add.R);           /* R^2 */
  blst_fp_sub(p3.X, p3.X, dbl.H);     /* X3 = R^2-H^2*sx */

  blst_fp_sub(p3.Y, p3.Y, p3.X);      /* H^2*U1-X3 */
  blst_fp_mul(p3.Y, p3.Y, add.R);     /* R*(H^2*U1-X3) */
  blst_fp_sub(p3.Y, p3.Y, dbl.R);     /* Y3 = R*(H^2*U1-X3)-H^3*S1 */

  vec_select(&p3, p1, &p3, sizeof(blst_p1), p2inf); 
  vec_select(out, p2, &p3, sizeof(blst_p1), p1inf); 
}
