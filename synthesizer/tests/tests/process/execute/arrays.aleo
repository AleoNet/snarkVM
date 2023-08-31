/*
randomness: 2937849
cases:
  - function: test_arrays
    inputs:
    - "[[true, false, true, false]]"
    - "[[false, true, false, true]]"

*/

program arrays.aleo;

struct tree:
    left as [[boolean; 4u32]; 1u32];
    right as [[boolean; 4u32]; 1u32];

function test_arrays:
    input r0 as [[boolean; 4u32]; 1u32].private;
    input r1 as [[boolean; 4u32]; 1u32].private;
    cast r0 r1 into r2 as tree;
    and r2.left[0u32][0u32] r2.right[0u32][0u32] into r3;
    and r2.left[0u32][1u32] r2.right[0u32][1u32] into r4;
    and r2.left[0u32][2u32] r2.right[0u32][2u32] into r5;
    and r2.left[0u32][3u32] r2.right[0u32][3u32] into r6;
    output r0 as [[boolean; 4u32]; 1u32].private;
    output r1 as [[boolean; 4u32]; 1u32].private;
    output r2 as tree.private;
    output r3 as boolean.private;
    output r4 as boolean.private;
    output r5 as boolean.private;
    output r6 as boolean.private;

