



program basic_math.aleo;

mapping add_uses...
mapping sub_uses...

function add_and_count:
    input r0 as i64.private;
    input r1 as i64.private;
    add r0 r1 into r2;
    async basic_math.aleo/add_and_count self.caller into r3;
    output r2;
    output r3;

finalize add_and_count:
    input r0 as address.public;
    get.or_use add_uses[r0] 0u64 into r1;
    add r1 1u64 into r2;
    set r2 into add_uses[r0];

function sub_and_count:
    input r0 as i64.private;
    input r1 as i64.private;
    sub r0 r1 into r2;
    async basic_math.aleo/sub_and_count self.caller into r3;
    output r2;
    output r3;

finalize sub_and_count:
    input r0 as address.public;
    get.or_use sub_uses[r0] 0u64 into r1;
    add r1 1u64 into r2;
    set r2 into sub_uses[r0];

///////

import basic_math.aleo;

program count_usages.aleo;

function add_and_subtract:
    input r0 as i64.private;
    input r1 as i64.private;
    call basic_math.aleo/add_and_count r0 r1 into r2 r3;
    call basic_math.aleo/sub_and_count r2 r1 into r4 r5;
    assert.eq r0 r2;
    future.input r3[0] into r6;
    future.input r5[0] into r7;
    assert.eq r6 r7;
    async count_usages.aleo/add_and_subtract r3 r5 into r8;
    output r0;
    output r8;

finalize add_and_subtract:
    input r0 as future.public;
    input r1 as future.public;
    await r0;
    await r1;
