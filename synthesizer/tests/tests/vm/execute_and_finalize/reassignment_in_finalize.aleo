/*
randomness: 123861083
cases:
  - program: reassignment_in_finalize.aleo
    function: test
    inputs: [1field, 2field]
*/

program reassignment_in_finalize.aleo;

function test:
    input r0 as field.public;
    input r1 as field.public;
    async test r0 r1 into r2;
    output r2 as reassignment_in_finalize.aleo/test.future;

finalize test:
    input r0 as field.public;
    input r1 as field.public;
    add r0 r1 into r2;
    add r2 r1 into r3;
    add r2 r1 into r2;
    assert.eq r2 r3;
