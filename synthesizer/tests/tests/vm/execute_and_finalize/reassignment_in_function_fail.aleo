/*
randomness: 98216932
cases: []
*/

program reassignment_in_function_fail.aleo;

function test:
    input r0 as field.private;
    input r1 as field.private;
    add r0 r1 into r0;
    output r0 as field.private;
