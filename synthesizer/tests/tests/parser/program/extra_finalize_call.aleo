import foo.aleo;

program extra_finalize_call_fail.aleo;

function test:
    input r0 as u8.public;
    input r1 as u8.public;
    call.function foo.aleo/bar r0 r1;
    call.function foo.aleo/baz r1 r2;
    finalize r0 r1;

finalize test:
    input r0 as u8.public;
    input r1 as u8.public;
    assert.neq r0 r1;
    call.finalize foo.aleo/bar r2 r3;
    call.finalize foo.aleo/baz r4 r5;
    call.finalize foo.aleo/baz r6 r7;
