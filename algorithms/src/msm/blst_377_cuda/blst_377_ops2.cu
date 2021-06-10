#include "blst_377_ops.h"
#include "types.h"
#include "asm_cuda.h"
#include <stdio.h>

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

__device__ void blst_inverse(blst_fp out, const blst_fp in) {
    if (is_blst_fp_zero(in)) {
        // this is really bad?
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
                // printf("c-tINVERSE ADDING b\n");
                blst_fp_add_unsafe(b, b, BLS12_377_P);
            }
            div_by_2_mod_384(b, b);
            // printf("c-t%i-inverse_round_u_stop: u=%llu b=%llu\n", threadIdx.x, u[0], b[0]);
        }

        while ((v[0] & 1) == 0) {
            // printf("c-t%i-inverse_round_v_start: u=%llu b=%llu\n", threadIdx.x, v[0], c[0]);
            div_by_2_mod_384(v, v);

            if ((c[0] & 1) != 0) {
                    // printf("c-tINVERSE ADDING c\n");
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
        blst_inverse(z_inv, in->Z);
        // printf("c-t%i:cinverse-out: %llu\n", threadIdx.x, z_inv[0]);
        blst_fp z_inv_squared;
        blst_fp_sqr(z_inv_squared, z_inv);
        blst_fp_mul(out->X, in->X, z_inv_squared);
        blst_fp_mul(z_inv_squared, z_inv_squared, z_inv);
        blst_fp_mul(out->Y, in->Y, z_inv_squared);
    }
}

__device__ void blstv2_add_affine_to_projective(blst_p1 *out, const blst_p1 *p1, const blst_p1_affine *p2) {
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

    // printf("c-t%llu:add:3 %llu\n", threadIdx.x, s2[0]);

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