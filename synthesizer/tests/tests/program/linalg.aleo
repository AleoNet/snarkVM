/*
randomness: 2937849
cases:
  - function: frobenius_inner_product
    inputs: [
        "[0field, 0field, 0field, 0field, 0field, 0field, 0field, 0field, 0field]",
        "[1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field]"
    ]
  - function: frobenius_inner_product
    inputs: [
        "[1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field]",
        "[1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field]"
    ]
  - function: matrix_multiply
    inputs: [
        "[1field, 1field, 0field, 1field, 0field, 1field, 1field, 0field, 1field]",
        "[0field, 1field, 0field, 1field, 1field, 0field, 0field, 0field, 1field]"
    ]
  - function: matrix_multiply
    inputs: [
        "[0field, 1field, 2field, 3field, 4field, 5field, 6field, 7field, 8field]",
        "[0field, 1field, 2field, 3field, 4field, 5field, 6field, 7field, 8field]"
    ]
*/

program linalg.aleo;

function frobenius_inner_product:
    input r0 as [field; 9].private;
    input r1 as [field; 9].private;
    mul r0[0] r1[0] into r2;
    mul r0[1] r1[1] into r3;
    mul r0[2] r1[2] into r4;
    mul r0[3] r1[3] into r5;
    mul r0[4] r1[4] into r6;
    mul r0[5] r1[5] into r7;
    mul r0[6] r1[6] into r8;
    mul r0[7] r1[7] into r9;
    mul r0[8] r1[8] into r10;
    add r2 r3 into r11;
    add r11 r4 into r12;
    add r12 r5 into r13;
    add r13 r6 into r14;
    add r14 r7 into r15;
    add r15 r8 into r16;
    add r16 r9 into r17;
    add r17 r10 into r18;
    output r18 as field.private;

function matrix_multiply:
    input r0 as [field; 9].private;
    input r1 as [field; 9].private;
    mul r0[0] r1[0] into r2;
    mul r0[1] r1[3] into r3;
    mul r0[2] r1[6] into r4;
    add r2 r3 into r5;
    add r5 r4 into r6;
    mul r0[0] r1[1] into r7;
    mul r0[1] r1[4] into r8;
    mul r0[2] r1[7] into r9;
    add r7 r8 into r10;
    add r10 r9 into r11;
    mul r0[0] r1[2] into r12;
    mul r0[1] r1[5] into r13;
    mul r0[2] r1[8] into r14;
    add r12 r13 into r15;
    add r15 r14 into r16;
    mul r0[3] r1[0] into r17;
    mul r0[4] r1[3] into r18;
    mul r0[5] r1[6] into r19;
    add r17 r18 into r20;
    add r20 r19 into r21;
    mul r0[3] r1[1] into r22;
    mul r0[4] r1[4] into r23;
    mul r0[5] r1[7] into r24;
    add r22 r23 into r25;
    add r25 r24 into r26;
    mul r0[3] r1[2] into r27;
    mul r0[4] r1[5] into r28;
    mul r0[5] r1[8] into r29;
    add r27 r28 into r30;
    add r30 r29 into r31;
    mul r0[6] r1[0] into r32;
    mul r0[7] r1[3] into r33;
    mul r0[8] r1[6] into r34;
    add r32 r33 into r35;
    add r35 r34 into r36;
    mul r0[6] r1[1] into r37;
    mul r0[7] r1[4] into r38;
    mul r0[8] r1[7] into r39;
    add r37 r38 into r40;
    add r40 r39 into r41;
    mul r0[6] r1[2] into r42;
    mul r0[7] r1[5] into r43;
    mul r0[8] r1[8] into r44;
    add r42 r43 into r45;
    add r45 r44 into r46;
    cast r6 r11 r16 r21 r26 r31 r36 r41 r46 into r47 as [field; 9];
    output r47 as [field; 9].private;






