/*
- [hello, 0u32, 1u32]
- [hello, 1u32, 2u32]
*/

program hello.aleo;

function hello:
    input r0 as u32.public;
    input r1 as u32.private;
    add r0 r1 into r2;
    output r2 as u32.private;
