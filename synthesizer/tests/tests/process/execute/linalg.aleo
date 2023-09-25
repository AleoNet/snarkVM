/*
randomness: 2937849
cases:
  - program: linalg.aleo
    function: frobenius_inner_product
    inputs:
    - "[[0field, 0field, 0field],
        [0field, 0field, 0field],
        [0field, 0field, 0field]]"
    - "[[1field, 1field, 1field],
        [1field, 1field, 1field],
        [1field, 1field, 1field]]"
  - program: linalg.aleo
    function: frobenius_inner_product
    inputs:
    - "[[1field, 1field, 1field],
        [1field, 1field, 1field],
        [1field, 1field, 1field]]"
    - "[[1field, 1field, 1field],
        [1field, 1field, 1field],
        [1field, 1field, 1field]]"

*/

program linalg.aleo;

function frobenius_inner_product:
    input r0 as [[field; 3u32]; 3u32].private;
    input r1 as [[field; 3u32]; 3u32].private;
    mul r0[0u32][0u32] r1[0u32][0u32] into r2;
    mul r0[0u32][1u32] r1[0u32][1u32] into r3;
    mul r0[0u32][2u32] r1[0u32][2u32] into r4;
    mul r0[1u32][0u32] r1[1u32][0u32] into r5;
    mul r0[1u32][1u32] r1[1u32][1u32] into r6;
    mul r0[1u32][2u32] r1[1u32][2u32] into r7;
    mul r0[2u32][0u32] r1[2u32][0u32] into r8;
    mul r0[2u32][1u32] r1[2u32][1u32] into r9;
    mul r0[2u32][2u32] r1[2u32][2u32] into r10;
    add r2 r3 into r11;
    add r11 r4 into r12;
    add r12 r5 into r13;
    add r13 r6 into r14;
    add r14 r7 into r15;
    add r15 r8 into r16;
    add r16 r9 into r17;
    add r17 r10 into r18;
    output r18 as field.private;

