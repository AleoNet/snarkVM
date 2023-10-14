/*
randomness: 0
cases:

  - program: abs.aleo
    function: abs_i8
    inputs: [0i8]
  - program: abs.aleo
    function: abs_i8
    inputs: [1i8]
  - program: abs.aleo
    function: abs_i8
    inputs: [10i8]
  - program: abs.aleo
    function: abs_i8
    inputs: [100i8]
  - program: abs.aleo
    function: abs_i8
    inputs: [127i8]
  - program: abs.aleo
    function: abs_i8
    inputs: [-1i8]
  - program: abs.aleo
    function: abs_i8
    inputs: [-10i8]
  - program: abs.aleo
    function: abs_i8
    inputs: [-100i8]
  - program: abs.aleo
    function: abs_i8
    inputs: [-127i8]
# negative test:
#  - program: abs.aleo
#    function: abs_i8
#    inputs: [-128i8]

  - program: abs.aleo
    function: abs_i16
    inputs: [0i16]
  - program: abs.aleo
    function: abs_i16
    inputs: [1i16]
  - program: abs.aleo
    function: abs_i16
    inputs: [1_000_i16]
  - program: abs.aleo
    function: abs_i16
    inputs: [10_000_i16]
  - program: abs.aleo
    function: abs_i16
    inputs: [32767_i16]
  - program: abs.aleo
    function: abs_i16
    inputs: [-1i16]
  - program: abs.aleo
    function: abs_i16
    inputs: [-1_000_i16]
  - program: abs.aleo
    function: abs_i16
    inputs: [-10_000_i16]
  - program: abs.aleo
    function: abs_i16
    inputs: [-32_767_i16]
  - program: abs.aleo
    function: abs_i16
    inputs: [-32_768_i16]

  - program: abs.aleo
    function: abs_i32
    inputs: [0i32]
  - program: abs.aleo
    function: abs_i32
    inputs: [1i32]
  - program: abs.aleo
    function: abs_i32
    inputs: [1_000_i32]
  - program: abs.aleo
    function: abs_i32
    inputs: [10_000_000_i32]
  - program: abs.aleo
    function: abs_i32
    inputs: [2_147_483_647_i32]
  - program: abs.aleo
    function: abs_i32
    inputs: [-1i32]
  - program: abs.aleo
    function: abs_i32
    inputs: [-1_000_i32]
  - program: abs.aleo
    function: abs_i32
    inputs: [-10_000_000_i32]
  - program: abs.aleo
    function: abs_i32
    inputs: [-2_147_483_647_i32]
  - program: abs.aleo
    function: abs_i32
    inputs: [-2_147_483_647_i32]

  - program: abs.aleo
    function: abs_i64
    inputs: [0i64]
  - program: abs.aleo
    function: abs_i64
    inputs: [1i64]
  - program: abs.aleo
    function: abs_i64
    inputs: [1_000_i64]
  - program: abs.aleo
    function: abs_i64
    inputs: [10_000_000_000_i64]
  - program: abs.aleo
    function: abs_i64
    inputs: [2_147_483_647_i64]
  - program: abs.aleo
    function: abs_i64
    inputs: [-1i64]
  - program: abs.aleo
    function: abs_i64
    inputs: [-1_000_i64]
  - program: abs.aleo
    function: abs_i64
    inputs: [-10_000_000_000_i64]
  - program: abs.aleo
    function: abs_i64
    inputs: [-9_223_372_036_854_775_807_i64]
  - program: abs.aleo
    function: abs_i64
    inputs: [-9_223_372_036_854_775_808_i64]

  - program: abs.aleo
    function: abs_i128
    inputs: [0i128]
  - program: abs.aleo
    function: abs_i128
    inputs: [1i128]
  - program: abs.aleo
    function: abs_i128
    inputs: [1_000_i128]
  - program: abs.aleo
    function: abs_i128
    inputs: [10_000_000_000_000_000_000_000_000_000_i128]
  - program: abs.aleo
    function: abs_i128
    inputs: [2_147_483_647_i128]
  - program: abs.aleo
    function: abs_i128
    inputs: [-1i128]
  - program: abs.aleo
    function: abs_i128
    inputs: [-1_000_i128]
  - program: abs.aleo
    function: abs_i128
    inputs: [-10_000_000_000_000_000_000_000_000_000_i128]
  - program: abs.aleo
    function: abs_i128
    inputs: [-170_141_183_460_469_231_731_687_303_715_884_105_727_i128]
  - program: abs.aleo
    function: abs_i128
    inputs: [-170_141_183_460_469_231_731_687_303_715_884_105_728_i128]

*/

program abs.aleo;

function abs_i8:
    input r0 as i8.private;
    abs r0 into r1;
    output r1 as i8.private;

function abs_i16:
    input r0 as i16.private;
    abs r0 into r1;
    output r1 as i16.private;

function abs_i32:
    input r0 as i32.private;
    abs r0 into r1;
    output r1 as i32.private;

function abs_i64:
    input r0 as i64.private;
    abs r0 into r1;
    output r1 as i64.private;

function abs_i128:
    input r0 as i128.private;
    abs r0 into r1;
    output r1 as i128.private;
