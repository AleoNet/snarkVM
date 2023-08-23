/*
cases:
  - function: hello
    inputs: [0u32, 1u32]
  - function: hello
    inputs: [1u32, 2u32]
*/
program correct_call_to_closure.aleo;

closure foo:
    input r0 as u32;
    input r1 as u32;
    add r0 r1 into r2;
    output r2 as u32;

function hello:
    input r0 as u32.public;
    input r1 as u32.private;
    call.closure foo r0 r1 into r2;
    output r2 as u32.private;


