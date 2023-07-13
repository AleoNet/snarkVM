/*
randomness: 8924529
cases:
  - function: test_arrays
    inputs: [0u8, 1u8, 2u8]
*/

program vectors.aleo;

function test_arrays:
    input r0 as u8.private;
    input r1 as u8.private;
    input r2 as u8.private;
    cast r0 into r3 as [u8; 1];
    cast r0 r1 into r4 as [u8; 2];
    cast r0 r1 r2 into r5 as [u8; 3];
    length r3 into r6;
    assert.eq r6 1u32;
    length r4 into r7;
    assert.eq r7 2u32;
    length r5 into r8;
    assert.eq r8 3u32;
    output r3 as [u8; 1].private;
    output r4 as [u8; 2].private;
    output r5 as [u8; 3].private;


