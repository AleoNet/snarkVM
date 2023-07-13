/*
randomness: 904820
cases:
  - function: empty_remove
    inputs: [10u8]
  - function: insert_contains_remove
    inputs: [0u8, 0u8]
  - function: insert_contains_remove
    inputs: [0u8, 0u8]
  - function: insert_contains_remove
    inputs: [0u8, 1u8]
*/

program mapping_operations.aleo;

mapping data:
    key left as u8.public;
    value right as u8.public;

function insert_contains_remove:
    input r0 as u8.public;
    input r1 as u8.public;
    finalize r0 r1;

finalize insert_contains_remove:
    input r0 as u8.public;
    input r1 as u8.public;
    contains data[r0] into r2;
    assert.eq r2 false;
    set r1 into data[r0];
    contains data[r0] into r3;
    assert.eq r3 true;
    remove data[r0];
    contains data[r0] into r4;
    assert.eq r4 false;

function empty_remove:
    input r0 as u8.public;
    finalize r0;

finalize empty_remove:
    input r0 as u8.public;
    remove data[r0];


