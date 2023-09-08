/*
randomness: 0
cases:
  - function: absw_i8
    inputs: [0i8]
  - function: absw_i8
    inputs: [1i8]
  - function: absw_i8
    inputs: [10i8]
  - function: absw_i8
    inputs: [100i8]
  - function: absw_i8
    inputs: [127i8]
  - function: absw_i8
    inputs: [-1i8]
  - function: absw_i8
    inputs: [-10i8]
  - function: absw_i8
    inputs: [-100i8]
  - function: absw_i8
    inputs: [-127i8]
  - function: absw_i8
    inputs: [-128i8]

  - function: absw_i16
    inputs: [0i16]
  - function: absw_i16
    inputs: [1i16]
  - function: absw_i16
    inputs: [1000i16]
  - function: absw_i16
    inputs: [10000i16]
  - function: absw_i16
    inputs: [32767i16]
  - function: absw_i16
    inputs: [-1i16]
  - function: absw_i16
    inputs: [-1000i16]
  - function: absw_i16
    inputs: [-10000i16]
  - function: absw_i16
    inputs: [-32767i16]
  - function: absw_i16
    inputs: [-32768i16]

  - function: absw_i32
    inputs: [0i32]
  - function: absw_i32
    inputs: [1i32]
  - function: absw_i32
    inputs: [1000i32]
  - function: absw_i32
    inputs: [10000000i32]
  - function: absw_i32
    inputs: [2147483647i32]
  - function: absw_i32
    inputs: [-1i32]
  - function: absw_i32
    inputs: [-1000i32]
  - function: absw_i32
    inputs: [-10000000i32]
  - function: absw_i32
    inputs: [-2147483647i32]
  - function: absw_i32
    inputs: [-2147483647i32]

  - function: absw_i64
    inputs: [0i64]
  - function: absw_i64
    inputs: [1i64]
  - function: absw_i64
    inputs: [1000i64]
  - function: absw_i64
    inputs: [10000000000i64]
  - function: absw_i64
    inputs: [2147483647i64]
  - function: absw_i64
    inputs: [-1i64]
  - function: absw_i64
    inputs: [-1000i64]
  - function: absw_i64
    inputs: [-10000000000i64]
  - function: absw_i64
    inputs: [-9223372036854775807i64]
  - function: absw_i64
    inputs: [-9223372036854775808i64]

  - function: absw_i128
    inputs: [0i128]
  - function: absw_i128
    inputs: [1i128]
  - function: absw_i128
    inputs: [1000i128]
  - function: absw_i128
    inputs: [10000000000000000000000000000i128]
  - function: absw_i128
    inputs: [2147483647i128]
  - function: absw_i128
    inputs: [-1i128]
  - function: absw_i128
    inputs: [-1000i128]
  - function: absw_i128
    inputs: [-10000000000000000000000000000i128]
  - function: absw_i128
    inputs: [-170141183460469231731687303715884105727i128]
  - function: absw_i128
    inputs: [-170141183460469231731687303715884105728i128]

*/

program absw.aleo;

function absw_i8:
    input r0 as i8.private;
    abs.w r0 into r1;
    output r1 as i8.private;

function absw_i16:
    input r0 as i16.private;
    abs.w r0 into r1;
    output r1 as i16.private;

function absw_i32:
    input r0 as i32.private;
    abs.w r0 into r1;
    output r1 as i32.private;

function absw_i64:
    input r0 as i64.private;
    abs.w r0 into r1;
    output r1 as i64.private;

function absw_i128:
    input r0 as i128.private;
    abs.w r0 into r1;
    output r1 as i128.private;
