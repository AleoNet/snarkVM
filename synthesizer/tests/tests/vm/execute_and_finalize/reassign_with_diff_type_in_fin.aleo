/*
randomness: 1239121
cases: []
*/

program reassign_with_diff_type_in_fin.aleo;

function test:
    input r0 as field.public;
    input r1 as field.public;
    async test r0 r1 into r2;
    output r2 as reassign_with_diff_type_in_fin.aleo/test.future;

finalize test:
    input r0 as field.public;
    input r1 as field.public;
    add r0 r1 into r2;
    add 0u8 1u8 into r2;
