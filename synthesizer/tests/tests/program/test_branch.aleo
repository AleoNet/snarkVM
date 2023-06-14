/*
randomness: 98372
cases:
  - function: run_test
    inputs: [0u8]
  - function: run_test
    inputs: [1u8]
*/

program test_branch.aleo;

function run_test:
    input r0 as u8.public;
    finalize r0;

finalize run_test:
    input r0 as u8.public;
    branch.eq r0 0u8 to exit;
    assert.eq true false;
    position exit;

