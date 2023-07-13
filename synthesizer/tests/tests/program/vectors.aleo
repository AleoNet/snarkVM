/*
randomness: 2544139
cases:
  - function: compare_vectors
    inputs: [0u8, 1u8, 2u8]
*/

program vectors.aleo;

mapping data:
    key left as u8.public;
    value right as [u8].public;

function compare_vectors:
    input r0 as u8.public;
    input r1 as u8.public;
    input r2 as u8.public;
    finalize r0 r1 r2;

finalize compare_vectors:
    input r0 as u8.public;
    input r1 as u8.public;
    input r2 as u8.public;
    cast into r3 as [u8];
    cast r0 r1 r2 into r4 as [u8];
    cast r0 r1 r2 into r5 as [u8];
    assert.neq r3 r4;
    assert.neq r3 r5;
    assert.eq r4 r5;
    length r3 into r6;
    assert.eq r6 0u32;
    length r4 into r7;
    assert.eq r7 3u32;
    length r5 into r8;
    assert.eq r8 3u32;


