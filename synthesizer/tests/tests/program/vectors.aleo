/*
randomness: 2544139
cases:
  - function: compare_vectors
    inputs: [0u8, 1u8, 2u8]
  - function: test_push
    inputs: [3u8, 4u8, 5u8]
  - function: test_delete
    inputs: [6u8, 7u8, 8u8]
  - function: test_get
    inputs: [9u8, 10u8, 11u8]

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

function test_push:
    input r0 as u8.public;
    input r1 as u8.public;
    input r2 as u8.public;
    finalize r0 r1 r2;

finalize test_push:
    input r0 as u8.public;
    input r1 as u8.public;
    input r2 as u8.public;
    cast into r3 as [u8];
    length r3 into r4;
    assert.eq r4 0u32;
    push r3 r0;
    length r3 into r5;
    assert.eq r5 1u32;
    push r3 r1;
    length r3 into r6;
    assert.eq r6 2u32;
    push r3 r2;
    length r3 into r7;
    assert.eq r7 3u32;

function test_delete:
    input r0 as u8.public;
    input r1 as u8.public;
    input r2 as u8.public;
    finalize r0 r1 r2;

finalize test_delete:
    input r0 as u8.public;
    input r1 as u8.public;
    input r2 as u8.public;
    cast r0 r1 r2 into r3 as [u8];
    length r3 into r4;
    assert.eq r4 3u32;
    delete r3 1u32 into r5;
    assert.eq r5 r1;
    length r3 into r6;
    assert.eq r6 2u32;
    delete r3 0u32 into r7;
    assert.eq r7 r0;
    length r3 into r8;
    assert.eq r8 1u32;
    delete r3 0u32 into r9;
    assert.eq r9 r2;
    length r3 into r10;
    assert.eq r10 0u32;

function test_get:
    input r0 as u8.public;
    input r1 as u8.public;
    input r2 as u8.public;
    finalize r0 r1 r2;

finalize test_get:
    input r0 as u8.public;
    input r1 as u8.public;
    input r2 as u8.public;
    cast r0 r1 r2 into r3 as [u8];
    index r3 0u32 into r4;
    assert.eq r4 r0;
    index r3 1u32 into r5;
    assert.eq r5 r1;
    index r3 2u32 into r6;
    assert.eq r6 r2;





