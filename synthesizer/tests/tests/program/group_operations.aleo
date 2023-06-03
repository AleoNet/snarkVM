/*
- [generator, 1scalar]
- [generator, 2scalar]
- [generator, 3scalar]
- [constant_ops]
*/

program group_operations.aleo;

function generator:
    input r0 as scalar.private;
    mul r0 group::GEN into r1;
    add r1 r1 into r2;
    double r1 into r3;
    output r1 as group.private;
    output r2 as group.private;
    output r3 as group.private;

function constant_ops:
    add group::GEN group::GEN into r0;
    double group::GEN into r1;
    output r0 as group.private;
    output r1 as group.private;

