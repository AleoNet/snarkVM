program foo.aleo;

function bar:
    input r0 as u8.public;
    input r1 as u8.public;
    add r0 r1 into r2;
    output r2 as u8.public;
    finalize r0 r1;

finalize bar:
    input r0 as u8.public;
    input r1 as u8.public;
    assert.neq r0 r1;

function baz:
    input r0 as u8.public;
    input r1 as u8.public;
    mul r0 r1 into r2;
    output r2 as u8.public;
    finalize r0 r1;

finalize baz:
    input r0 as u8.public;
    input r1 as u8.public;
    assert.neq r0 r1;
