program matrix.aleo;

function frobenius_inner_product:
    input r0 as [[field; 3]; 3].public;
    input r1 as [[field; 3]; 3].private;
    add r0[0][0] r1[0][0] into r2;
    add r0[0][1] r1[0][1] into r3;
    add r0[0][2] r1[0][2] into r4;
    add r0[1][0] r1[1][0] into r5;
    add r0[1][1] r1[1][1] into r6;
    add r0[1][2] r1[1][2] into r7;
    add r0[2][0] r1[2][0] into r8;
    add r0[2][1] r1[2][1] into r9;
    add r0[2][2] r1[2][2] into r10;
    add r2 r3 into r11;
    add r11 r4 into r12;
    add r12 r5 into r13;
    add r13 r6 into r14;
    add r14 r7 into r15;
    add r15 r8 into r16;
    add r16 r9 into r17;
    add r17 r10 into r18;
    output r18 as field.private;
