/*
randomness: 479283
cases:
  - function: rand_chacha_with_literals
    inputs: [0scalar, 0group, 0u8, 2i16, 4u32, 7i64, 8u128, 10field]
  - function: rand_chacha_with_struct
    inputs: ["{ first: 0field, second: 0field, third: 0field, fourth: 0field, fifth: 0field }"]
  - function: rand_chacha_check
    inputs: [0field, false]
  - function: rand_chacha_check
    inputs: [1field, true]
*/

program test_rand.aleo;

struct bundle:
    first as field;
    second as field;
    third as field;
    fourth as field;
    fifth as field;

function rand_chacha_with_struct:
    input r0 as bundle.public;
    finalize r0;

finalize rand_chacha_with_struct:
    input r0 as bundle.public;
    rand.chacha r0 into r1 as field;

function rand_chacha_check:
    input r0 as field.public;
    input r1 as boolean.public;
    finalize r0 r1;

finalize rand_chacha_check:
    input r0 as field.public;
    input r1 as boolean.public;
    rand.chacha r0 into r2 as boolean;
    assert.eq r1 r2;

function rand_chacha_with_literals:
    input r0 as scalar.public;
    input r1 as group.public;
    input r2 as u8.public;
    input r3 as i16.public;
    input r4 as u32.public;
    input r5 as i64.public;
    input r6 as u128.public;
    input r7 as field.public;
    finalize r0 r1 r2 r3 r4 r5 r6 r7;

finalize rand_chacha_with_literals:
    input r0 as scalar.public;
    input r1 as group.public;
    input r2 as u8.public;
    input r3 as i16.public;
    input r4 as u32.public;
    input r5 as i64.public;
    input r6 as u128.public;
    input r7 as field.public;
    rand.chacha into r8 as boolean;
    rand.chacha into r9 as scalar;
    rand.chacha into r10 as group;
    rand.chacha into r11 as u8;
    rand.chacha into r12 as i16;
    rand.chacha into r13 as u32;
    rand.chacha into r14 as i64;
    rand.chacha into r15 as u128;
    rand.chacha into r16 as field;
    rand.chacha r0 into r17 as scalar;
    rand.chacha r1 into r18 as group;
    rand.chacha r2 into r19 as u8;
    rand.chacha r3 into r20 as i16;
    rand.chacha r4 into r21 as u32;
    rand.chacha r5 into r22 as i64;
    rand.chacha r6 into r23 as u128;
    rand.chacha r7 into r24 as field;
    rand.chacha r0 r1 into r25 as scalar;
    rand.chacha r1 r2 into r26 as group;
    rand.chacha r2 r3 into r27 as u8;
    rand.chacha r3 r4 into r28 as i16;
    rand.chacha r4 r5 into r29 as u32;
    rand.chacha r5 r6 into r30 as i64;
    rand.chacha r6 r7 into r31 as u128;
