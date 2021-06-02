#include "blst_377_ops.h"

/* BLS12-377 P - Modulus */
const blst_fp BLS12_377_P = {
  TO_LIMB_T(0x8508c00000000001), TO_LIMB_T(0x170b5d4430000000),
  TO_LIMB_T(0x1ef3622fba094800), TO_LIMB_T(0x1a22d9f300f5138f),
  TO_LIMB_T(0xc63b05c06ca1493b), TO_LIMB_T(0x1ae3a4617c510ea)
};

/* R = (1 << 384) % P */
#define ONE_MONT_P TO_LIMB_T(0x02cdffffffffff68), \
                 TO_LIMB_T(0x51409f837fffffb1), \
                 TO_LIMB_T(0x9f7db3a98a7d3ff2), \
                 TO_LIMB_T(0x7b4e97b76e7c6305), \
                 TO_LIMB_T(0x4cf495bf803c84e8), \
                 TO_LIMB_T(0x008d6661e2fdf49a)

const blst_fp BLS12_377_ONE = { /* (1<<384)%P, "radix", one-in-Montgomery */
  ONE_MONT_P
  //TO_LIMB_T(0x02cdffffffffff68), TO_LIMB_T(0x51409f837fffffb1),
  //TO_LIMB_T(0x9f7db3a98a7d3ff2), TO_LIMB_T(0x7b4e97b76e7c6305),
  //TO_LIMB_T(0x4cf495bf803c84e8), TO_LIMB_T(0x008d6661e2fdf49a)
};

/* MU = -1 / P  (INV) (p0) */
/* (-modinv(P, 2^64)) % 2^64 */
const limb_t BLS12_377_p0 = (limb_t)0x8508bfffffffffff;  /* -1/P */

/* G1 Generator in Montgomery form */
const blst_p1 BLS12_377_G1_MONT = {
  { TO_LIMB_T(0x260f33b9772451f4), TO_LIMB_T(0xc54dd773169d5658),
  TO_LIMB_T(0x5c1551c469a510dd), TO_LIMB_T(0x761662e4425e1698),
  TO_LIMB_T(0xc97d78cc6f065272), TO_LIMB_T(0xa41206b361fd4d) },
  { TO_LIMB_T(0x8193961fb8cb81f3), TO_LIMB_T(0x638d4c5f44adb8),
  TO_LIMB_T(0xfafaf3dad4daf54a), TO_LIMB_T(0xc27849e2d655cd18),
  TO_LIMB_T(0x2ec3ddb401d52814), TO_LIMB_T(0x7da93326303c71) },
  { ONE_MONT_P }
};

const blst_p1_affine BLS12_377_G1_MONT_AFFINE = {
  { TO_LIMB_T(0x260f33b9772451f4), TO_LIMB_T(0xc54dd773169d5658),
  TO_LIMB_T(0x5c1551c469a510dd), TO_LIMB_T(0x761662e4425e1698),
  TO_LIMB_T(0xc97d78cc6f065272), TO_LIMB_T(0xa41206b361fd4d) },
  { TO_LIMB_T(0x8193961fb8cb81f3), TO_LIMB_T(0x638d4c5f44adb8),
  TO_LIMB_T(0xfafaf3dad4daf54a), TO_LIMB_T(0xc27849e2d655cd18),
  TO_LIMB_T(0x2ec3ddb401d52814), TO_LIMB_T(0x7da93326303c71) }
};

const blst_scalar BLS12_377_r = {
  TO_LIMB_T(0x0a11800000000001), TO_LIMB_T(0x59aa76fed0000001),
  TO_LIMB_T(0x60b44d1e5c37b001), TO_LIMB_T(0x12ab655e9a2ca556)
};

const blst_scalar BLS12_377_rRR = {
  TO_LIMB_T(0x25d577bab861857b), TO_LIMB_T(0xcc2c27b58860591f),
  TO_LIMB_T(0xa7cc008fe5dc8593), TO_LIMB_T(0x11fdae7eff1c939)
};

static inline void vec_select(void *ret, const void *a, const void *b,
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

static inline bool is_zero(limb_t l)
{   return (~l & (l - 1)) >> (LIMB_T_BITS - 1);   }

static inline bool vec_is_zero(const void *a, size_t num)
{
  const limb_t *ap = (const limb_t *)a;
  limb_t acc;
  size_t i;

  num /= sizeof(limb_t);

  for (acc = 0, i = 0; i < num; i++)
    acc |= ap[i];

  return is_zero(acc);
}

static inline void vec_copy(void *restrict ret, const void *a, size_t num)
{
  limb_t *rp = (limb_t *)ret;
  const limb_t *ap = (const limb_t *)a;
  size_t i;

  num /= sizeof(limb_t);

  for (i = 0; i < num; i++)
    rp[i] = ap[i];
}

static inline void vec_zero(void *ret, size_t num)
{
    volatile limb_t *rp = (volatile limb_t *)ret;
    size_t i;

    num /= sizeof(limb_t);

    for (i = 0; i < num; i++)
        rp[i] = 0;

#if defined(__GNUC__) && !defined(__NVCC__)
    asm volatile("" : : "r"(ret) : "memory");
#endif
}

static inline bool vec_is_equal(const void *a, const void *b, size_t num)
{
  const limb_t *ap = (const limb_t *)a;
  const limb_t *bp = (const limb_t *)b;
  limb_t acc;
  size_t i;

  num /= sizeof(limb_t);

  for (acc = 0, i = 0; i < num; i++)
    acc |= ap[i] ^ bp[i];

  return is_zero(acc);
}

static inline bool is_bit_set(const byte *v, size_t i)
{   return (v[i/8] >> (i%8)) & 1;   }

/*
 * Addition with affine point that can handle doubling [as well as
 * points at infinity, with |p1| being encoded as Z==0 and |p2| as
 * X,Y==0] in constant time. But at what additional cost? Best
 * addition result is 7M+4S, while this routine takes 8M+5S, as per
 *
 * -------------+-------------
 * addition     | doubling
 * -------------+-------------
 * U1 = X1      | U1 = X2
 * U2 = X2*Z1^2 |
 * S1 = Y1      | S1 = Y2
 * S2 = Y2*Z1^3 |
 * H = U2-X1    | H' = 2*Y2
 * R = S2-Y1    | R' = 3*X2^2[+a]
 * sx = X1+U2   | sx = X2+X2
 * zz = H*Z1    | zz = H'
 * -------------+-------------
 * H!=0 || R!=0 | H==0 && R==0
 *
 *      X3 = R^2-H^2*sx
 *      Y3 = R*(H^2*U1-X3)-H^3*S1
 *      Z3 = zz
 *
 * As for R!=0 condition in context of H==0, a.k.a. P-P. The result is
 * infinity by virtue of Z3 = (U2-U1)*zz = H*zz = 0*zz == 0.
 */
void blst_p1_add_or_double_affine(blst_p1 *out, const blst_p1 *p1,
                                                const blst_p1_affine *p2) {
  blst_p1 p3; /* starts as (,, H*Z1) from addition side */
  struct { blst_fp H, R, sx; } add, dbl; 
  bool p1inf, p2inf, is_dbl; 

  p2inf = vec_is_zero(p2->X, 2*sizeof(p2->X)); 
  if (p2inf) {
    vec_copy(out, p1, sizeof(blst_p1));
    return;
  }
  p1inf = vec_is_zero(p1->Z, sizeof(p1->Z));
  if (p1inf) {
    vec_copy(out->X, p2, 2*sizeof(p2->X));
    vec_copy(out->Z, BLS12_377_ONE, sizeof(out->Z));
    return;
  }

  blst_fp_add(dbl.sx, p2->X, p2->X);  /* sx = X2+X2 */
  blst_fp_sqr(dbl.R, p2->X);          /* X2^2 */
  blst_fp_mul_by_3(dbl.R, dbl.R);     /* R = 3*X2^2 */
  blst_fp_add(dbl.H, p2->Y, p2->Y);   /* H = 2*Y2 */

  blst_fp_sqr(add.H, p1->Z);          /* Z1^2 */
  blst_fp_mul(add.R, add.H, p1->Z);   /* Z1^3 */
  blst_fp_mul(add.R, add.R, p2->Y);   /* S2 = Y2*Z1^3 */
  blst_fp_sub(add.R, add.R, p1->Y);   /* R = S2-Y1 */

  blst_fp_mul(add.H, add.H, p2->X);   /* U2 = X2*Z1^2 */

  blst_fp_add(add.sx, add.H, p1->X);  /* sx = X1+U2 */
  blst_fp_sub(add.H, add.H, p1->X);   /* H = U2-X1 */

  blst_fp_mul(p3.Z, add.H, p1->Z);    /* Z3 = H*Z1 */

  /* make the choice between addition and doubling */ 
  is_dbl = vec_is_zero(add.H, 2*sizeof(add.H));       
  vec_select(p3.X, p2, p1, 2*sizeof(p3.X), is_dbl);   
  vec_select(p3.Z, dbl.H, p3.Z, sizeof(p3.Z), is_dbl);
  vec_select(&add, &dbl, &add, sizeof(add), is_dbl);  
  /* |p3| and |add| hold all inputs now, |p3| will hold output */

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

  vec_select(p3.X, p2,  p3.X, 2*sizeof(p3.X), p1inf); 
  vec_select(p3.Z, BLS12_377_ONE, p3.Z, sizeof(p3.Z), p1inf); 
  vec_select(out, p1, &p3, sizeof(blst_p1), p2inf); 
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
void blst_p1_add_or_double(blst_p1 *out, const blst_p1 *p1,
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


/*
 * https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
 */
void blst_p1_double(blst_p1 *out, const blst_p1 *p1) { 
  blst_fp A, B, C;

  blst_fp_sqr(A, p1->X);              /* A = X1^2 */
  blst_fp_sqr(B, p1->Y);              /* B = Y1^2 */
  blst_fp_sqr(C, B);                  /* C = B^2 */

  blst_fp_add(B, B, p1->X);           /* X1+B */
  blst_fp_sqr(B, B);                  /* (X1+B)^2 */
  blst_fp_sub(B, B, A);               /* (X1+B)^2-A */
  blst_fp_sub(B, B, C);               /* (X1+B)^2-A-C */
  blst_fp_add(B, B, B);               /* D = 2*((X1+B)^2-A-C) */

  blst_fp_mul_by_3(A, A);             /* E = 3*A */

  blst_fp_sqr(out->X, A);             /* F = E^2 */
  blst_fp_sub(out->X, out->X, B);       
  blst_fp_sub(out->X, out->X, B);     /* X3 = F-2*D */

  blst_fp_add(out->Z, p1->Z, p1->Z);  /* 2*Z1 */
  blst_fp_mul(out->Z, out->Z, p1->Y); /* Z3 = 2*Z1*Y1 */

  blst_fp_mul_by_8(C, C);             /* 8*C */
  blst_fp_sub(out->Y, B, out->X);     /* D-X3 */
  blst_fp_mul(out->Y, out->Y, A);     /* E*(D-X3) */
  blst_fp_sub(out->Y, out->Y, C);     /* Y3 = E*(D-X3)-8*C */
}

bool blst_p1_is_inf(const blst_p1 *p)
{   return vec_is_zero(p->Z, sizeof(p->Z));   }


/*
 * http://www.hyperelliptic.org/EFD/g1p/auto-shortw-xyzz.html#doubling-mdbl-2008-s-1
 */
void blst_p1_ext_double_affine(blst_p1_ext *out, const blst_p1_affine *p1) {
  blst_fp U, S, M;
  
  blst_fp_add(U, p1->Y, p1->Y);        /* U = 2 * Y1 */
  blst_fp_sqr(out->ZZ, U);             /* V (ZZ3) = U^2 */
  blst_fp_mul(out->ZZZ, U, out->ZZ);   /* W = U * V */
  blst_fp_mul(S, p1->X, out->ZZ);      /* S = X1 * V */
  blst_fp_sqr(M, p1->X);               /* X1^2 */
  blst_fp_mul_by_3(M, M);              /* M = 3 * X1^2 + a (here a == 0) */
  blst_fp_sqr(out->X, M);              /* M^2 */
  blst_fp_sub(out->X, out->X, S);      /* M^2 - S */
  blst_fp_sub(out->X, out->X, S);      /* X3 = M^2 - 2 * S */
  blst_fp_sub(out->Y, S, out->X);      /* S - X3 */
  blst_fp_mul(out->Y, out->Y, M);      /* M * (S - X3) */
  blst_fp_mul(U, out->ZZZ, p1->Y);     /* W * Y1 */
  blst_fp_sub(out->Y, out->Y, U);      /* Y3 = M * (S - X3) - W * Y1 */
}

/*
 * http://www.hyperelliptic.org/EFD/g1p/auto-shortw-xyzz.html#addition-madd-2008-s
 */
void blst_p1_ext_add_or_double_affine(blst_p1_ext *out, const blst_p1_ext *p1,
                                      const blst_p1_affine *p2)
{

  if (vec_is_zero(p2->X, 2*sizeof(p2->X))) {  /* p2 == inf */
    vec_copy(out, p1, sizeof(blst_p1_ext));
    return;
  }

  if (vec_is_zero(p1->ZZ, sizeof(p1->ZZ))) {  /* p1 == inf */
    vec_copy(out->X, p2, 2*sizeof(p2->X));
    vec_copy(out->ZZ, BLS12_377_ONE, sizeof(out->ZZ));
    vec_copy(out->ZZZ, BLS12_377_ONE, sizeof(out->ZZZ));
    return;
  }

  blst_fp PPP, R, PP, Q, RR, Q2;
  
  blst_fp_mul(PPP, p2->X, p1->ZZ);     /* U2 = X2 * ZZ1  */
  blst_fp_mul(R, p2->Y, p1->ZZZ);      /* S2 = Y2 * ZZZ1 */
  blst_fp_sub(PPP, PPP, p1->X);        /* P  = U2 - X1   */
  blst_fp_sub(R, R, p1->Y);            /* R  = S2 - Y1   */
  
  if (vec_is_zero(PPP, sizeof(PPP))) { 
    if (vec_is_zero(R, sizeof(R))) { 
      blst_p1_ext_double_affine(out, p2); 
      return;
    }
    vec_zero(out->ZZ, 2*sizeof(out->ZZ));
    return;
  }

  blst_fp_sqr(PP, PPP);                /* PP = P^2 */
  blst_fp_mul(PPP, PPP, PP);           /* PPP = P * PP */
  blst_fp_mul(Q, p1->X, PP);           /* Q = X1 * PP */
  blst_fp_sqr(RR, R);                  /* RR = R^2 */
  blst_fp_add(Q2, Q, Q);               /* Q2 = 2 * Q */
  blst_fp_sub(out->X, RR, PPP);        /* R^2 - PPP  */
  blst_fp_sub(out->X, out->X, Q2);     /* X3 = R^2 - PPP - 2 * Q */
  blst_fp_mul(out->Y, p1->Y, PPP);     /* Y1 * PPP */
  blst_fp_sub(Q, Q, out->X);           /* Q - X3 */
  blst_fp_mul(R, R, Q);                /* R * (Q - X3) */
  blst_fp_sub(out->Y, R, out->Y);      /* Y3 = R * (Q - X3) - Y1 * PPP */
  blst_fp_mul(out->ZZ, p1->ZZ, PP);    /* ZZ3 = ZZ1 * PP */
  blst_fp_mul(out->ZZZ, p1->ZZZ, PPP); /* ZZZ3 = ZZZ1 * PPP */
}

/*
 *  Jacobian (X, Y, Z) : x = X / Z^2, y = Y / Z^3 
 *  Extended Jacobian (X, Y, ZZ, ZZZ) : x = X / ZZ, y = Y / ZZZ, ZZ^3 = ZZZ^2 
 *  Do not check for infinity (used in cases where check is already done)
 */
void blst_p1_from_extended_no_check(blst_p1 *out, const blst_p1_ext *in)
{
  blst_fp_mul(out->X, in->X, in->ZZ);     /* X * ZZ */
  blst_fp_mul(out->X, out->X, in->ZZ);    /* X * ZZ * ZZ */
  blst_fp_mul(out->Y, in->Y, in->ZZZ);    /* Y * ZZZ */
  blst_fp_mul(out->Y, out->Y, in->ZZZ);   /* Y * ZZZ * ZZZ */
  vec_copy(out->Z, in->ZZZ, sizeof(out->Z));
}

bool blst_p1_ext_is_inf(const blst_p1_ext *p)
{   return vec_is_zero(p->ZZ, sizeof(p->ZZ));   }
