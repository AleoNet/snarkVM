import foo.aleo;

program function_and_finalize_match.aleo;

function test:
    input r0 as u8.public;
    input r1 as u8.public;
    call.function foo.aleo/bar r0 r1 into r2;
    call.function foo.aleo/baz r1 r2 into r3;
    finalize r0 r1;

finalize test:
    input r0 as u8.public;
    input r1 as u8.public;
    add r0 r1 into r2;
    add r1 r2 into r3;
    call.finalize foo.aleo/bar r2 r3;
    add r2 r3 into r4;
    add r3 r4 into r5;
    call.finalize foo.aleo/baz r4 r5;
    add r0 r4 into r6;
    add r1 r5 into r7;
    assert.eq r4 r6;
    assert.eq r5 r7;
