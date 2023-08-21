/*
randomness: 12345
cases:
  - function: hello
    inputs: [0u32, 1u32]
  - function: hello
    inputs: [1u32, 2u32]
  - function: goodbye
    inputs: [0u32, 1u32]
  - function: goodbye
    inputs: [1u32, 0u32]
*/

program hello.aleo;

function hello:
    input r0 as u32.public;
    input r1 as u32.private;
    add r0 r1 into r2;
    output r2 as u32.private;

function goodbye:
    input r0 as u32.public;
    input r1 as u32.private;
    add r0 r1 into r2;
    output r2 as u32.public;
    finalize r1 r2;

finalize goodbye:
    input r0 as u32.public;
    input r1 as u32.public;
    add r0 r1 into r2;
    assert.neq r1 r2;
