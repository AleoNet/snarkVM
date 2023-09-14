/*
randomness: 2937849
cases:
  - function: test_array_cast
    inputs:
    - "[[true, false, true, false]]"
    - "[[false, true, false, true]]"
  - function: test_array_concat
    inputs:
    - "[[true, true, true, true]]"
    - "[[false, false, false, false]]"

*/

program arrays_in_finalize.aleo;

struct tree:
    left as [[boolean; 4u32]; 1u32];
    right as [[boolean; 4u32]; 1u32];

function test_array_cast:
    input r0 as [[boolean; 4u32]; 1u32].public;
    input r1 as [[boolean; 4u32]; 1u32].public;
    cast r0 r1 into r2 as tree;
    and r2.left[0u32][0u32] r2.right[0u32][0u32] into r3;
    and r2.left[0u32][1u32] r2.right[0u32][1u32] into r4;
    and r2.left[0u32][2u32] r2.right[0u32][2u32] into r5;
    and r2.left[0u32][3u32] r2.right[0u32][3u32] into r6;
    cast r3 r4 r5 r6 into r7 as [boolean; 4u32];
    cast r7 into r8 as [[boolean; 4u32]; 1u32];
    output r8 as [[boolean; 4u32]; 1u32].public;
    output r2 as tree.private;
    finalize r0 r1;

finalize test_array_cast:
    input r0 as [[boolean; 4u32]; 1u32].public;
    input r1 as [[boolean; 4u32]; 1u32].public;
    and r0[0u32][0u32] r1[0u32][0u32] into r2;
    and r0[0u32][1u32] r1[0u32][1u32] into r3;
    and r0[0u32][2u32] r1[0u32][2u32] into r4;
    and r0[0u32][3u32] r1[0u32][3u32] into r5;
    cast r2 r3 r4 r5 into r6 as [boolean; 4u32];
    cast r6 into r7 as [[boolean; 4u32]; 1u32];
    assert.eq r7[0u32][0u32] false;
    assert.eq r7[0u32][1u32] false;
    assert.eq r7[0u32][2u32] false;
    assert.eq r7[0u32][3u32] false;

function test_array_concat:
    input r0 as [[boolean; 4u32]; 1u32].public;
    input r1 as [[boolean; 4u32]; 1u32].public;
    finalize r0 r1;

finalize test_array_concat:
    input r0 as [[boolean; 4u32]; 1u32].public;
    input r1 as [[boolean; 4u32]; 1u32].public;
    concat r0 r1 into r2 as [[boolean; 4u32]; 2u32];
    concat r0[0u32] r1[0u32] into r3 as [boolean; 8u32];
    assert.eq r2[0u32][0u32] r3[0u32];
    assert.eq r2[0u32][1u32] r3[1u32];
    assert.eq r2[0u32][2u32] r3[2u32];
    assert.eq r2[0u32][3u32] r3[3u32];
    assert.eq r2[1u32][0u32] r3[4u32];
    assert.eq r2[1u32][1u32] r3[5u32];
    assert.eq r2[1u32][2u32] r3[6u32];
    assert.eq r2[1u32][3u32] r3[7u32];






