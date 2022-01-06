#include "blst_377_ops.h"
#include "types.h"
#include "asm_cuda.h"
#include <stdio.h>

__device__ const blst_p1 BLS12_377_ZERO_PROJECTIVE = {
  {0},
  {ONE_MONT_P},
  {0}
};

__device__ const blst_p1_affine BLS12_377_ZERO_AFFINE = {
  {0},
  {ONE_MONT_P}
};

__device__ const blst_scalar BLS12_377_R = {
  TO_LIMB_T(0x0a11800000000001), TO_LIMB_T(0x59aa76fed0000001),
  TO_LIMB_T(0x60b44d1e5c37b001), TO_LIMB_T(0x12ab655e9a2ca556)
};

__device__ static inline int is_blst_p1_zero(const blst_p1 *p) {
    return p->Z[0] == 0 &&
        p->Z[1] == 0 &&
        p->Z[2] == 0 &&
        p->Z[3] == 0 &&
        p->Z[4] == 0 &&
        p->Z[5] == 0;
}

__device__ static inline int is_blst_fp_zero(const blst_fp p) {
    return p[0] == 0 &&
        p[1] == 0 &&
        p[2] == 0 &&
        p[3] == 0 &&
        p[4] == 0 &&
        p[5] == 0;
}

__device__ static inline int is_blst_fp_eq(const blst_fp p1, const blst_fp p2) {
    return p1[0] == p2[0] &&
        p1[1] == p2[1] &&
        p1[2] == p2[2] &&
        p1[3] == p2[3] &&
        p1[4] == p2[4] &&
        p1[5] == p2[5];
}

__device__ static inline int is_blst_p1_affine_zero(const blst_p1_affine *p) {
    return p->X[0] == 0 &&
        p->X[1] == 0 &&
        p->X[2] == 0 &&
        p->X[3] == 0 &&
        p->X[4] == 0 &&
        p->X[5] == 0;
}

__device__ static const blst_fp BIGINT_ONE = { 1, 0, 0, 0, 0, 0 };

__device__ void blst_fp_inverse(blst_fp out, const blst_fp in) {
    if (is_blst_fp_zero(in)) {
        // this is really bad
        *((int*)NULL);
    }
    // Guajardo Kumar Paar Pelzl
    // Efficient Software-Implementation of Finite Fields with Applications to
    // Cryptography
    // Algorithm 16 (BEA for Inversion in Fp)

    blst_fp u;
    memcpy(u, in, sizeof(blst_fp));
    blst_fp v;
    memcpy(v, BLS12_377_P, sizeof(blst_fp));
    blst_fp b;
    memcpy(b, BLS12_377_R2, sizeof(blst_fp));
    blst_fp c;
    memset(c, 0, sizeof(blst_fp));

    while (!is_blst_fp_eq(u, BIGINT_ONE) && !is_blst_fp_eq(v, BIGINT_ONE)) {
        // printf("c-t%i-inverse_round: u=%llu v=%llu b=%llu c=%llu\n", threadIdx.x, u[0], v[0], b[0], c[0]);
        while ((u[0] & 1) == 0) {
            // printf("c-t%i-inverse_round_u_start: u=%llu b=%llu\n", threadIdx.x, u[0], b[0]);
            div_by_2_mod_384(u, u);

            if ((b[0] & 1) != 0) {
                blst_fp_add_unsafe(b, b, BLS12_377_P);
            }
            div_by_2_mod_384(b, b);
            // printf("c-t%i-inverse_round_u_stop: u=%llu b=%llu\n", threadIdx.x, u[0], b[0]);
        }

        while ((v[0] & 1) == 0) {
            // printf("c-t%i-inverse_round_v_start: u=%llu b=%llu\n", threadIdx.x, v[0], c[0]);
            div_by_2_mod_384(v, v);

            if ((c[0] & 1) != 0) {
                blst_fp_add_unsafe(c, c, BLS12_377_P);
            }
            div_by_2_mod_384(c, c);
            // printf("c-t%i-inverse_round_v_stop: u=%llu b=%llu\n", threadIdx.x, v[0], c[0]);
        }

        if (is_gt_384(u, v)) {
            blst_fp_sub_unsafe(u, u, v);
            
            blst_fp_sub(b, b, c);
        } else {
            blst_fp_sub_unsafe(v, v, u);

            blst_fp_sub(c, c, b);
        }
    }
    if (is_blst_fp_eq(u, BIGINT_ONE)) {
        memcpy(out, b, sizeof(blst_fp));
    } else {
        memcpy(out, c, sizeof(blst_fp));
    }
}

__device__ void blst_p1_projective_into_affine(blst_p1_affine* out, const blst_p1* in) {
    if (is_blst_p1_zero(in)) {
        memset(out->X, 0, sizeof(blst_fp));
        memcpy(out->Y, BLS12_377_ONE, sizeof(blst_fp));
        //todo: set inf
    } else if (is_blst_fp_eq(in->Z, BLS12_377_ONE)) {
        memcpy(out->X, in->X, sizeof(blst_fp));
        memcpy(out->Y, in->Y, sizeof(blst_fp));
    } else {
        blst_fp z_inv;
        // printf("c-t%i:cinverse-in: %llu\n", threadIdx.x, in->Z[0]);
        blst_fp_inverse(z_inv, in->Z);
        // printf("c-t%i:cinverse-out: %llu\n", threadIdx.x, z_inv[0]);
        blst_fp z_inv_squared;
        blst_fp_sqr(z_inv_squared, z_inv);
        blst_fp_mul(out->X, in->X, z_inv_squared);
        blst_fp_mul(z_inv_squared, z_inv_squared, z_inv);
        blst_fp_mul(out->Y, in->Y, z_inv_squared);
    }
}

__device__ void blst_p1_double(blst_p1* out, const blst_p1* in) {
    if (is_blst_p1_zero(in)) {
        memcpy(out, in, sizeof(blst_p1));
    }

    // Z3 = 2*Y1*Z1
    blst_fp_mul(out->Z, in->Y, in->Z);
    blst_fp_add(out->Z, out->Z, out->Z);

    // A = X1^2
    blst_fp a;
    blst_fp_sqr(a, in->X);
    
    // B = Y1^2
    blst_fp b;
    blst_fp_sqr(b, in->Y);

    // C = B^2
    blst_fp c;
    blst_fp_sqr(c, b);

    // D = 2*((X1+B)^2-A-C)
    blst_fp d;
    blst_fp_add(d, in->X, b);
    blst_fp_sqr(d, d);
    blst_fp_sub(d, d, a);
    blst_fp_sub(d, d, c);
    blst_fp_add(d, d, d);

    // E = 3*A
    blst_fp e;
    blst_fp_add(e, a, a);
    blst_fp_add(e, e, a);

    // F = E^2
    blst_fp f;
    blst_fp_sqr(f, e);

    // X3 = F-2*D
    blst_fp_add(out->X, d, d);
    blst_fp_sub(out->X, f, out->X);

    // Y3 = E*(D-X3)-8*C
    blst_fp_sub(out->Y, d, out->X);
    blst_fp_mul(out->Y, out->Y, e);

    blst_fp c3;
    blst_fp_add(c3, c, c); // 2c
    blst_fp_add(c3, c3, c3); // 4c
    blst_fp_add(c3, c3, c3); // 8c
    blst_fp_sub(out->Y, out->Y, c3);
}

__device__ void blst_p1_double_affine(blst_p1* out, const blst_p1_affine* p) {
    /*
        dbl-2009-l from
        http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
    */

    // A = X1^2
    blst_fp A;
    blst_fp_sqr(A, p->X);

    // B = Y1^2
    blst_fp B;
    blst_fp_sqr(B, p->Y);

    // C = B^2
    blst_fp C;
    blst_fp_sqr(C, B);

    // D = 2 * ((X1 + B)^2 - A - C)
    blst_fp X1B;
    blst_fp_add(X1B, p->X, B);
    blst_fp_sqr(X1B, X1B);
    blst_fp_sub(X1B, X1B, A);
    blst_fp_sub(X1B, X1B, C);
    blst_fp D;
    blst_fp_add(D, X1B, X1B);

    // E = 3 * A
    blst_fp E;
    blst_fp_add(E, A, A);
    blst_fp_add(E, E, A);

    // F = E^2
    blst_fp F;
    blst_fp_sqr(F, E);

    // X3 = F - 2*D
    memcpy(out->X, F, sizeof(blst_fp));
    blst_fp_sub(out->X, out->X, D);
    blst_fp_sub(out->X, out->X, D);

    // Y3 = E*(D - X3) - 8*C
    blst_fp C8;
    blst_fp_add(C8, C, C);
    blst_fp_add(C8, C8, C8);
    blst_fp_add(C8, C8, C8);
    blst_fp_sub(D, D, out->X);
    blst_fp_mul(E, E, D);
    blst_fp_sub(out->Y, E, C8);

    // Z3 = 2*Y1
    blst_fp_add(out->Z, p->Y, p->Y);
}

__device__ void blst_p1_add_affine_to_projective(blst_p1 *out, const blst_p1 *p1, const blst_p1_affine *p2) {
    if (is_blst_p1_affine_zero(p2)) {
        memcpy(out, p1, sizeof(blst_p1));
        return;
    }

    if (is_blst_p1_zero(p1)) {
        memcpy(out->X, p2->X, sizeof(blst_fp));
        memcpy(out->Y, p2->Y, sizeof(blst_fp));
        memcpy(out->Z, BLS12_377_ONE, sizeof(blst_fp));
        return;
    }
  
    // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl
    // Works for all curves.

    // printf("c-t%llu:add:0 %llu,%llu,%llu -> %llu,%llu\n", threadIdx.x, p1->X[0], p1->Y[0], p1->Z[0], p2->X[0], p2->Y[0]);

    // Z1Z1 = Z1^2
    blst_fp z1z1;
    blst_fp_sqr(z1z1, p1->Z);

    // printf("c-t%llu:add:1 %llu\n", threadIdx.x, z1z1[0]);

    // U2 = X2*Z1Z1
    blst_fp u2;
    blst_fp_mul(u2, p2->X, z1z1);

    // printf("c-t%llu:add:2 %llu\n", threadIdx.x, u2[0]);

    // S2 = Y2*Z1*Z1Z1
    blst_fp s2;
    blst_fp_mul(s2, p2->Y, p1->Z);
    blst_fp_mul(s2, s2, z1z1);

    if (is_blst_fp_eq(p1->X, u2) && is_blst_fp_eq(p1->Y, s2)) {
        blst_p1_double(out, p1);
        return;
    }

    // printf("c-t%llu:add:3 %llu\n", threadIdx.x, s2[0]);

    // printf("c-t%llu:add:pre-4 %llu - %llu\n", threadIdx.x, u2[0], p1->X[0]);
    // H = U2-X1
    blst_fp h;
    blst_fp_sub(h, u2, p1->X);

    // printf("c-t%llu:add:4 %llu\n", threadIdx.x, h[0]);

    // HH = H^2
    blst_fp hh;
    blst_fp_sqr(hh, h);
    // printf("c-t%llu:add:5 %llu\n", threadIdx.x, hh[0]);

    // I = 4*HH
    blst_fp i;
    memcpy(i, hh, sizeof(blst_fp));
    blst_fp_add(i, i, i);
    blst_fp_add(i, i, i);
    // printf("c-t%llu:add:6 %llu\n", threadIdx.x, i[0]);

    // J = H*I
    blst_fp j;
    blst_fp_mul(j, h, i);
    // printf("c-t%llu:add:7 %llu\n", threadIdx.x, j[0]);

    // r = 2*(S2-Y1)
    blst_fp r;
    blst_fp_sub(r, s2, p1->Y);
    blst_fp_add(r, r, r);
    // printf("c-t%llu:add:8 %llu\n", threadIdx.x, r[0]);

    // V = X1*I
    blst_fp v;
    blst_fp_mul(v, p1->X, i);
    // printf("c-t%llu:add:9 %llu\n", threadIdx.x, v[0]);

    // X3 = r^2 - J - 2*V
    blst_fp_sqr(out->X, r);
    // printf("c-t%llu:add:1X %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, out->X[0], out->X[1], out->X[2], out->X[3], out->X[4], out->X[5]);
    blst_fp_sub(out->X, out->X, j);
    // printf("c-t%llu:add:2X %llu, %llu, %llu, %llu, %llu, %llu -- %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, out->X[0], out->X[1], out->X[2], out->X[3], out->X[4], out->X[5], j[0], j[1], j[2], j[3], j[4], j[5]);
    blst_fp_sub(out->X, out->X, v);
    // printf("c-t%llu:add:3X %llu\n", threadIdx.x, out->X[0]);
    blst_fp_sub(out->X, out->X, v);
    // printf("c-t%llu:add:4X %llu\n", threadIdx.x, out->X[0]);

    // Y3 = r*(V-X3)-2*Y1*J
    blst_fp_mul(j, p1->Y, j);
    blst_fp_add(j, j, j);
    blst_fp_sub(out->Y, v, out->X);
    blst_fp_mul(out->Y, out->Y, r);
    blst_fp_sub(out->Y, out->Y, j);
    // printf("c-t%llu:add:Y %llu\n", threadIdx.x, out->Y[0]);

    // Z3 = (Z1+H)^2-Z1Z1-HH
    blst_fp_add(out->Z, p1->Z, h);
    blst_fp_sqr(out->Z, out->Z);
    blst_fp_sub(out->Z, out->Z, z1z1);
    blst_fp_sub(out->Z, out->Z, hh);
    // printf("c-t%llu:add:Z %llu\n", threadIdx.x, out->Z[0]);
}


__device__ void blst_p1_add_projective_to_projective(blst_p1 *out, const blst_p1 *p1, const blst_p1 *p2) {
    if (is_blst_p1_zero(p2)) {
        memcpy(out, p1, sizeof(blst_p1));
        return;
    }

    if (is_blst_p1_zero(p1)) {
        memcpy(out, p2, sizeof(blst_p1));
        return;
    }

    int p1_is_affine = is_blst_fp_eq(p1->Z, BLS12_377_ONE);
    int p2_is_affine = is_blst_fp_eq(p2->Z, BLS12_377_ONE);
    //todo: confirm generated ptx here is *okay* for warp divergence
    if (p1_is_affine && p2_is_affine) {
        blst_p1_affine p1_affine;
        memcpy(&p1_affine.X, &p1->X, sizeof(blst_fp));
        memcpy(&p1_affine.Y, &p1->Y, sizeof(blst_fp));
        blst_p1_affine p2_affine;
        memcpy(&p2_affine.X, &p2->X, sizeof(blst_fp));
        memcpy(&p2_affine.Y, &p2->Y, sizeof(blst_fp));
        blst_p1_add_affines_into_projective(out, &p1_affine, &p2_affine);
        return;
    } if (p1_is_affine) {
        blst_p1_affine p1_affine;
        memcpy(&p1_affine.X, &p1->X, sizeof(blst_fp));
        memcpy(&p1_affine.Y, &p1->Y, sizeof(blst_fp));
        blst_p1_add_affine_to_projective(out, p2, &p1_affine);
        return;
    } else if (p2_is_affine) {
        blst_p1_affine p2_affine;
        memcpy(&p2_affine.X, &p2->X, sizeof(blst_fp));
        memcpy(&p2_affine.Y, &p2->Y, sizeof(blst_fp));
        blst_p1_add_affine_to_projective(out, p1, &p2_affine);
        return;
    }
  
    // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl
    // Works for all curves.

    // printf("c-t%llu:add:0 %llu,%llu,%llu -> %llu,%llu\n", threadIdx.x, p1->X[0], p1->Y[0], p1->Z[0], p2->X[0], p2->Y[0]);

    // Z1Z1 = Z1^2
    blst_fp z1z1;
    blst_fp_sqr(z1z1, p1->Z);

    // Z2Z2 = Z2^2
    blst_fp z2z2;
    blst_fp_sqr(z2z2, p2->Z);

    // U1 = X1*Z2Z2
    blst_fp u1;
    blst_fp_mul(u1, p1->X, z2z2);

    // U2 = X2*Z1Z1
    blst_fp u2;
    blst_fp_mul(u2, p2->X, z1z1);

    // S1 = Y1*Z2*Z2Z2
    blst_fp s1;
    blst_fp_mul(s1, p1->Y, p2->Z);
    blst_fp_mul(s1, s1, z2z2);

    // S2 = Y2*Z1*Z1Z1
    blst_fp s2;
    blst_fp_mul(s2, p2->Y, p1->Z);
    blst_fp_mul(s2, s2, z1z1);

    // H = U2-U1
    blst_fp h;
    blst_fp_sub(h, u2, u1);

    // printf("c-t%llu:add:4 %llu\n", threadIdx.x, h[0]);

    // HH = H^2
    blst_fp hh;
    blst_fp_sqr(hh, h);
    // printf("c-t%llu:add:5 %llu\n", threadIdx.x, hh[0]);

    // I = 4*HH
    blst_fp i;
    memcpy(i, hh, sizeof(blst_fp));
    blst_fp_add(i, i, i);
    blst_fp_add(i, i, i);
    // printf("c-t%llu:add:6 %llu\n", threadIdx.x, i[0]);

    // J = H*I
    blst_fp j;
    blst_fp_mul(j, h, i);
    // printf("c-t%llu:add:7 %llu\n", threadIdx.x, j[0]);

    // r = 2*(S2-S1)
    blst_fp r;
    blst_fp_sub(r, s2, s1);
    blst_fp_add(r, r, r);
    // printf("c-t%llu:add:8 %llu\n", threadIdx.x, r[0]);

    // V = U1*I
    blst_fp v;
    blst_fp_mul(v, u1, i);
    // printf("c-t%llu:add:9 %llu\n", threadIdx.x, v[0]);

    // X3 = r^2 - J - 2*V
    blst_fp_sqr(out->X, r);
    // printf("c-t%llu:add:1X %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, out->X[0], out->X[1], out->X[2], out->X[3], out->X[4], out->X[5]);
    blst_fp_sub(out->X, out->X, j);
    // printf("c-t%llu:add:2X %llu, %llu, %llu, %llu, %llu, %llu -- %llu, %llu, %llu, %llu, %llu, %llu\n", threadIdx.x, out->X[0], out->X[1], out->X[2], out->X[3], out->X[4], out->X[5], j[0], j[1], j[2], j[3], j[4], j[5]);
    blst_fp_sub(out->X, out->X, v);
    // printf("c-t%llu:add:3X %llu\n", threadIdx.x, out->X[0]);
    blst_fp_sub(out->X, out->X, v);
    // printf("c-t%llu:add:4X %llu\n", threadIdx.x, out->X[0]);

    // Y3 = r*(V-X3)-2*S1*J
    blst_fp_mul(j, s1, j);
    blst_fp_add(j, j, j);
    blst_fp_sub(out->Y, v, out->X);
    blst_fp_mul(out->Y, out->Y, r);
    blst_fp_sub(out->Y, out->Y, j);
    // printf("c-t%llu:add:Y %llu\n", threadIdx.x, out->Y[0]);

    // Z3 = ((Z1+Z2)^2-Z1Z1-Z2Z2)*H
    blst_fp_add(out->Z, p1->Z, p2->Z);
    blst_fp_sqr(out->Z, out->Z);
    blst_fp_sub(out->Z, out->Z, z1z1);
    blst_fp_sub(out->Z, out->Z, z2z2);
    blst_fp_mul(out->Z, out->Z, h);
    // printf("c-t%llu:add:Z %llu\n", threadIdx.x, out->Z[0]);
}

__device__ void blst_p1_add_affines_into_projective(blst_p1* out, const blst_p1_affine* p1, const blst_p1_affine* p2) {
    /*
        mmadd-2007-bl from
        http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-mmadd-2007-bl
    */

    // The points can't be 0.
    if (is_blst_p1_affine_zero(p2)) {
        memcpy(out->X, p1->X, sizeof(blst_fp));
        memcpy(out->Y, p1->Y, sizeof(blst_fp));

        if (is_blst_p1_affine_zero(p1)) {
            memcpy(out->Z, BLS12_377_ZERO, sizeof(blst_fp));
        } else {
            memcpy(out->Z, BLS12_377_ONE, sizeof(blst_fp));
        }

        return;
    } else if (is_blst_p1_affine_zero(p1)) {
        memcpy(out->X, p2->X, sizeof(blst_fp));
        memcpy(out->Y, p2->Y, sizeof(blst_fp));

        if (is_blst_p1_affine_zero(p2)) {
            memcpy(out->Z, BLS12_377_ZERO, sizeof(blst_fp));
        } else {
            memcpy(out->Z, BLS12_377_ONE, sizeof(blst_fp));
        }

        return;
    }

    // mmadd-2007-bl does not support equal values for p1 and p2.
    // If `p1` and `p2` are equal, use the doubling algorithm.
    if(is_blst_fp_eq(p1->X, p2->X) && is_blst_fp_eq(p1->Y, p2->Y)) {
        blst_p1_double_affine(out, p1);
        return;
    }

    // H = X2-X1
    blst_fp h;
    blst_fp_sub(h, p2->X, p1->X);

    // HH = H^2
    // I = 4*HH
    blst_fp i;
    memcpy(i, h, sizeof(blst_fp));
    blst_fp_add(i, i, i);
    blst_fp_sqr(i, i);

    // J = H*I
    blst_fp j;
    blst_fp_mul(j, h, i);

    // r = 2*(Y2-Y1)
    blst_fp r;
    blst_fp_sub(r, p2->Y, p1->Y);
    blst_fp_add(r, r, r);

    // V = X1*I
    blst_fp v;
    blst_fp_mul(v, p1->X, i);

    // X3 = r^2-J-2*V
    blst_fp_sqr(out->X, r);
    blst_fp_sub(out->X, out->X, j);
    blst_fp_sub(out->X, out->X, v);
    blst_fp_sub(out->X, out->X, v);

    // Y3 = r*(V-X3)-2*Y1*J
    blst_fp_sub(out->Y, v, out->X);
    blst_fp_mul(out->Y, out->Y, r);

    blst_fp y1j;
    blst_fp_mul(y1j, p1->Y, j);
    blst_fp_sub(out->Y, out->Y, y1j);
    blst_fp_sub(out->Y, out->Y, y1j);

    // Z3 = 2*H
    blst_fp_add(out->Z, h, h);
}

__device__ void blst_p1_add_affine_to_affine(blst_p1_affine* out, const blst_p1_affine* p1, const blst_p1_affine* p2) {
    /*
        http://www.hyperelliptic.org/EFD/g1p/auto-shortw.html
        x3 = (y2-y1)2/(x2-x1)2-x1-x2
        y3 = (2*x1+x2)*(y2-y1)/(x2-x1)-(y2-y1)3/(x2-x1)3-y1
    */
    blst_fp y_diff;
    blst_fp_sub(y_diff, p2->Y, p1->Y);

    blst_fp y_diff2;
    blst_fp_sqr(y_diff2, y_diff);

    blst_fp x_diff_inv;
    blst_fp_sub(x_diff_inv, p2->X, p1->X);
    blst_fp_inverse(x_diff_inv, x_diff_inv);
    
    blst_fp x_diff_inv2;
    blst_fp_sqr(x_diff_inv2, x_diff_inv);

    blst_fp sum_x;
    blst_fp_add(sum_x, p1->X, p2->X);

    blst_fp_mul(out->X, y_diff2, x_diff_inv2);
    blst_fp_sub(out->X, out->X, sum_x);

    blst_fp_mul(out->Y, y_diff, x_diff_inv);
    blst_fp_mul(out->Y, out->Y, sum_x);
    blst_fp_add(out->Y, out->Y, out->Y);

    blst_fp y_diff3;
    blst_fp_mul(y_diff3, y_diff2, y_diff);

    blst_fp x_diff_inv3;
    blst_fp_mul(x_diff_inv3, x_diff_inv2, x_diff_inv);

    blst_fp j;
    blst_fp_mul(j, y_diff3, x_diff_inv3);
    blst_fp_sub(out->Y, out->Y, j);

    blst_fp_sub(out->Y, out->Y, p1->Y);
}
