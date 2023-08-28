/*
cases:
  - function: lock
    inputs: []
  - function: lock
    inputs: []
*/

program timelock.aleo;

function lock:
    finalize;

finalize lock:
    gt block.height 4u32 into r0; // It takes 4 blocks to set up the test.
    assert.eq r0 true;
