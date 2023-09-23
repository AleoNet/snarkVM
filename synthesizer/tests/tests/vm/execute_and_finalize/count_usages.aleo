/*
randomness: 490582958
cases: []
*/

program basic_math.aleo;

mapping uses:
    key user as address.public;
    value count as i64.public;

function add_and_count:
    input r0 as i64.private;
    input r1 as i64.private;
    add r0 r1 into r2;
    finalize add_and_count self.caller into r3;
    output r2 as i64.private;
    output r3 as future;

finalize add_and_count:
    input r0 as address.public;
    get.or_use uses[r0] 0u64 into r1;
    add r1 1u64 into r2;
    set r2 into uses[r0];

function sub_and_count:
    input r0 as i64.private;
    input r1 as i64.private;
    sub r0 r1 into r2;
    finalize self.caller into r3;
    output r2 as i64.private;
    output r3 as future;

finalize sub_and_count:
    input r0 as address.public;
    get.or_use uses[r0] 0u64 into r1;
    add r1 1u64 into r2;
    set r2 into uses[r0];
