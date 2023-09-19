program call_in_closure.aleo;

closure bar:
    input r0 as u32;
    input r1 as u32;
    add r0 r1 into r2;
    output r2 as u32;

closure foo:
    input r0 as u32;
    input r1 as u32;
    call.closure bar r0 r1 into r2;
    output r2 as u32;

function hello:
    input r0 as u32.public;
    input r1 as u32.private;
    call.closure foo r0 r1 into r2;
    output r2 as u32.private;
