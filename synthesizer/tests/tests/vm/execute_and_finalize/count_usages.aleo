/*
randomness: 904282498
cases:
  - program: count_usages.aleo
    function: add_and_subtract
    inputs:
    - [1i64, 1i64]
*/

program math.aleo;

mapping add_uses:
    key owner as address.public;
    value count as u64.public;

mapping sub_uses:
    key owner as address.public;
    value count as u64.public;

function add_and_count:
    input r0 as i64.private;
    input r1 as i64.private;
    add.w r0 r1 into r2;
    output r2 as i64.private;
    finalize self.caller;

finalize add_and_count:
    input r0 as address.public;
    get.or_use add_uses[r0] 0u64 into r1;
    add r1 1u64 into r2;
    set r2 into add_uses[r0];

function sub_and_count:
    input r0 as i64.private;
    input r1 as i64.private;
    sub.w r0 r1 into r2;
    output r2 as i64.private;
    finalize self.caller;

finalize sub_and_count:
    input r0 as address.public;
    get.or_use sub_uses[r0] 0u64 into r1;
    add r1 1u64 into r2;
    set r2 into sub_uses[r0];


/////////////////////////////////////////////////

import math.aleo;

program count_usages.aleo;

function add_and_subtract:
    input r0 as i64.private;
    input r1 as i64.private;
    call.function math.aleo/add_and_count r0 r1 into r2;
    call.function math.aleo/sub_and_count r0 r1 into r3;
    assert.eq r0 r3;
    finalize;


finalize add_and_subtract:
    call.finalize math.aleo/add_and_count r0;
    call.finalize math.aleo/sub_and_count r1;

