/*
randomness: 123861083
cases:
  - program: reassignment_in_finalize.aleo
    function: test
    inputs: [1field, 2field]
  - program: reassignment_in_finalize.aleo
    function: double_divide
    inputs: [8field, 2field, 2field, 2field]
  - program: reassignment_in_finalize.aleo
    function: double_divide
    inputs: [100field, 0field, 0field, 1field]
  - program: reassignment_in_finalize.aleo
    function: double_divide
    inputs: [100field, 0field, 0field, 0field]
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

function double_divide:
    input r0 as field.public;
    input r1 as field.public;
    input r2 as field.public;
    input r3 as field.public;
    async double_divide r0 r1 r2 r3 into r4;
    output r4 as reassignment_in_finalize.aleo/double_divide.future;

finalize double_divide:
    input r0 as field.public;
    input r1 as field.public;
    input r2 as field.public;
    input r3 as field.public;
    // If `r1` is zero, then divide `r0` by 10, otherwise divide by `r1`.
    branch.eq r1 0field to else_branch_0;
    div r0 r1 into r4;
    branch.eq true true to end_0;
    position else_branch_0;
    div r0 10field into r4;
    position end_0;
    // If `r2` is zero, then divide `r3` by 10, otherwise divide by `r2`.
    branch.eq r2 0field to else_branch_1;
    div r4 r2 into r5;
    branch.eq true true to end_1;
    position else_branch_1;
    div r4 10field into r5;
    position end_1;
    // Check that `r5` matches `r3`.
    assert.eq r5 r3;



