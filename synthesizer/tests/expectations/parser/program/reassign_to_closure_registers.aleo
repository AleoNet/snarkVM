program reassign_to_closure_registers.aleo;

closure hello:
    input r0 as u32;
    input r1 as u32;
    add r0 r1 into r2;
    add r1 r2 into r2;
    output r2 as u32;

function main:
    input r0 as u32.public;
    input r1 as u32.private;
    call hello r0 r1 into r2;
    output r2 as u32.private;
