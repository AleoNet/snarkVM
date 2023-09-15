/*
cases: []
*/

program incorrect_call_to_closure_fail.aleo;

closure foo:
    input r0 as u32;
    input r1 as u32;
    add r0 r1 into r2;
    output r2 as u32;

function hello:
    input r0 as u32.public;
    input r1 as u32.private;
    call.function foo r0 r1 into r2;
    output r2 as u32.private;
