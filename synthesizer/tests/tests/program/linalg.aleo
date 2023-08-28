/*
randomness: 2937849
cases:
  - function: frobenius_inner_product
    inputs: [
        [0field, 0field, 0field, 0field, 0field, 0field, 0field, 0field, 0field],
        [1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field]
    ]
  - function: frobenius_inner_product
    inputs: [
        [1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field],
        [1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field, 1field]
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

