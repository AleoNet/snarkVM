program reassign_to_function_registers.aleo;

function hello:
    input r0 as u32.public;
    input r1 as u32.public;
    finalize r0 r1;

finalize hello:
    input r0 as u32.public;
    input r1 as u32.public;
    add r0 r1 into r2;
    add r1 r2 into r2;
