/*
randomness: 902384
cases:
  - program: lossy_casts.aleo
    function: test_lossy_cast
    inputs: [79363714989903307245735717098563574705733591463163614225748337416674727625843187853442697973404985688481508350822field]
  - program: lossy_casts.aleo
    function: test_lossy_cast
    inputs: [0field]
  - program: lossy_casts.aleo
    function: test_lossy_cast
    inputs: [1field]
  - program: lossy_casts.aleo
    function: test_lossy_cast
    inputs: [340_282_366_920_938_463_463_374_607_431_768_211_456field]
  - program: lossy_casts.aleo
    function: test_lossy_cast
    inputs: [340_282_366_920_938_463_463_374_607_431_768_211_457field]


*/

program lossy_casts.aleo;

function test_lossy_cast:
    input r0 as field.private;
    cast.lossy r0 into r1 as u128;
    cast.lossy r0 into r2 as i128;
    cast.lossy r0 into r3 as u64;
    cast.lossy r0 into r4 as i64;
    cast.lossy r0 into r5 as u32;
    cast.lossy r0 into r6 as i32;
    cast.lossy r0 into r7 as u16;
    cast.lossy r0 into r8 as i16;
    cast.lossy r0 into r9 as u8;
    cast.lossy r0 into r10 as i8;
    cast.lossy r0 into r11 as boolean;
    cast.lossy r0 into r12 as group;
    output r1 as u128.private;
    output r2 as i128.private;
    output r3 as u64.private;
    output r4 as i64.private;
    output r5 as u32.private;
    output r6 as i32.private;
    output r7 as u16.private;
    output r8 as i16.private;
    output r9 as u8.private;
    output r10 as i8.private;
    output r11 as boolean.private;
    output r12 as group.private;
