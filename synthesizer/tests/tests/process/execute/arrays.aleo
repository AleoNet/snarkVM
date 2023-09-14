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

program arrays.aleo;

struct tree:
    left as [[boolean; 4u32]; 1u32];
    right as [[boolean; 4u32]; 1u32];

function test_array_cast:
    input r0 as [[boolean; 4u32]; 1u32].private;
    input r1 as [[boolean; 4u32]; 1u32].private;
    cast r0 r1 into r2 as tree;
    and r2.left[0u32][0u32] r2.right[0u32][0u32] into r3;
    and r2.left[0u32][1u32] r2.right[0u32][1u32] into r4;
    and r2.left[0u32][2u32] r2.right[0u32][2u32] into r5;
    and r2.left[0u32][3u32] r2.right[0u32][3u32] into r6;
    cast r3 r4 r5 r6 into r7 as [boolean; 4u32];
    cast r7 into r8 as [[boolean; 4u32]; 1u32];
    output r8 as [[boolean; 4u32]; 1u32].private;
    output r2 as tree.private;

function test_array_concat:
    input r0 as [[boolean; 4u32]; 1u32].private;
    input r1 as [[boolean; 4u32]; 1u32].private;
    concat r0 r1 into r2 as [[boolean; 4u32]; 2u32];
    concat r0[0u32] r1[0u32] into r3 as [boolean; 8u32];
    output r2 as [[boolean; 4u32]; 2u32].private;
    output r3 as [boolean; 8u32].private;



