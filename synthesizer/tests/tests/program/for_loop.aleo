/*
randomness: 909217
cases:
  - function: run_test
    inputs: [0u32, 0u32]
  - function: run_test
    inputs: [10u32, 45u32]
  - function: run_test
    inputs: [100u32, 4950u32]
*/

program for_loop.aleo;

function run_test:
    input r0 as u32.public;
    input r1 as u32.public;
    finalize r0 r1;

finalize run_test:
    input r0 as u32.public;
    input r1 as u32.public;
    add 0u32 0u32 into r2;
    for r3 in 0u32..r0:
        add r2 r3 into r2;
    end.for;
    assert.eq r1 r2;
