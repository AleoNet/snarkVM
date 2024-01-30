/*
randomness: 1239121
cases: []
*/

program reassign_to_input_in_fin_fail.aleo;

function test:
    input r0 as field.public;
    input r1 as field.public;
    async test r0 r1 into r2;
    output r2 as reassign_to_input_in_fin_fail.aleo/test.future;

finalize test:
    input r0 as field.public;
    input r1 as field.public;
    add 1u8 2u8 into r0;
