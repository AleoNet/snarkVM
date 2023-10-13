/*

randomness: 0

cases:

  - program: addw.aleo
    function: addw_i8
    inputs: [6i8, 9i8]
  - program: addw.aleo
    function: addw_i8
    inputs: [-100i8, -10i8]
  - program: addw.aleo
    function: addw_i8
    inputs: [0i8, 0i8]
  - program: addw.aleo
    function: addw_i8
    inputs: [50i8, -40i8]
  - program: addw.aleo
    function: addw_i8
    inputs: [-70i8, 30i8]
  - program: addw.aleo
    function: addw_i8
    inputs: [120i8, 50i8]

  - program: addw.aleo
    function: addw_i16
    inputs: [10_000_i16, 20_000_i16]
  - program: addw.aleo
    function: addw_i16
    inputs: [-10_000_i16, -20_000_i16]
  - program: addw.aleo
    function: addw_i16
    inputs: [10_000_i16, -20_000_i16]
  - program: addw.aleo
    function: addw_i16
    inputs: [-10_000_i16, 20_000_i16]
  - program: addw.aleo
    function: addw_i16
    inputs: [-20_000_i16, -20_000_i16]

  - program: addw.aleo
    function: addw_i32
    inputs: [10_000_000_i32, 20_000_000_i32]
  - program: addw.aleo
    function: addw_i32
    inputs: [-10_000_000_i32, -20_000_000_i32]
  - program: addw.aleo
    function: addw_i32
    inputs: [10_000_000_i32, -20_000_000_i32]
  - program: addw.aleo
    function: addw_i32
    inputs: [-10_000_000_i32, 20_000_000_i32]
  - program: addw.aleo
    function: addw_i32
    inputs: [2_000_000_000_i32, 2_000_000_000_i32]

  - program: addw.aleo
    function: addw_i64
    inputs: [10_000_000_000_000_i64, 20_000_000_000_000_i64]
  - program: addw.aleo
    function: addw_i64
    inputs: [-10_000_000_000_000_i64, -20_000_000_000_000_i64]
  - program: addw.aleo
    function: addw_i64
    inputs: [10_000_000_000_000_i64, -20_000_000_000_000_i64]
  - program: addw.aleo
    function: addw_i64
    inputs: [-10_000_000_000_000_i64, 20_000_000_000_000_i64]
  - program: addw.aleo
    function: addw_i64
    inputs: [9_000_000_000_000_000_000_i64, 8_000_000_000_000_000_000_i64]

  - program: addw.aleo
    function: addw_i128
    inputs: [10_000_000_000_000_000_000_000_i128, 20_000_000_000_000_000_000_000_i128]
  - program: addw.aleo
    function: addw_i128
    inputs: [-10_000_000_000_000_000_000_000_i128, -20_000_000_000_000_000_000_000_i128]
  - program: addw.aleo
    function: addw_i128
    inputs: [10_000_000_000_000_000_000_000_i128, -20_000_000_000_000_000_000_000_i128]
  - program: addw.aleo
    function: addw_i128
    inputs: [-10_000_000_000_000_000_000_000_i128, 20_000_000_000_000_000_000_000_i128]
  - program: addw.aleo
    function: addw_i128
    inputs: [85_070_591_730_234_615_865_843_651_857_942_052_864_i128, 85_070_591_730_234_615_865_843_651_857_942_052_864_i128]

  - program: addw.aleo
    function: addw_u8
    inputs: [6u8, 9u8]
  - program: addw.aleo
    function: addw_u8
    inputs: [100u8, 120u8]
  - program: addw.aleo
    function: addw_u8
    inputs: [0u8, 0u8]
  - program: addw.aleo
    function: addw_u8
    inputs: [120u8, 200u8]

  - program: addw.aleo
    function: addw_u16
    inputs: [10_000_u16, 20_000_u16]
  - program: addw.aleo
    function: addw_u16
    inputs: [30_000_u16, 20_000_u16]
  - program: addw.aleo
    function: addw_u16
    inputs: [40_000_u16, 40_000_u16]

  - program: addw.aleo
    function: addw_u32
    inputs: [10_000_000_u32, 20_000_000_u32]
  - program: addw.aleo
    function: addw_u32
    inputs: [2_500_000_000_u32, 1_500_000_000_u32]
  - program: addw.aleo
    function: addw_u32
    inputs: [3_000_000_000_u32, 2_000_000_000_u32]

  - program: addw.aleo
    function: addw_u64
    inputs: [10_000_000_000_000_u64, 20_000_000_000_000_u64]
  - program: addw.aleo
    function: addw_u64
    inputs: [7_000_000_000_000_000_000_u64, 10_000_000_000_000_000_000_u64]
  - program: addw.aleo
    function: addw_u64
    inputs: [10_000_000_000_000_000_000_u64, 9_000_000_000_000_000_000_u64]

  - program: addw.aleo
    function: addw_u128
    inputs: [10_000_000_000_000_000_000_000_u128, 20_000_000_000_000_000_000_000_u128]
  - program: addw.aleo
    function: addw_u128
    inputs: [200_000_000_000_000_000_000_000_000_000_000_000_000_u128, 100_000_000_000_000_000_000_000_000_000_000_000_000_u128]
  - program: addw.aleo
    function: addw_u128
    inputs: [200_000_000_000_000_000_000_000_000_000_000_000_000_u128, 200_000_000_000_000_000_000_000_000_000_000_000_000_u128]

*/

program addw.aleo;

function addw_i8:
    input r0 as i8.private;
    input r1 as i8.private;
    add.w r0 r1 into r2;
    output r2 as i8.private;

function addw_i16:
    input r0 as i16.private;
    input r1 as i16.private;
    add.w r0 r1 into r2;
    output r2 as i16.private;

function addw_i32:
    input r0 as i32.private;
    input r1 as i32.private;
    add.w r0 r1 into r2;
    output r2 as i32.private;

function addw_i64:
    input r0 as i64.private;
    input r1 as i64.private;
    add.w r0 r1 into r2;
    output r2 as i64.private;

function addw_i128:
    input r0 as i128.private;
    input r1 as i128.private;
    add.w r0 r1 into r2;
    output r2 as i128.private;

function addw_u8:
    input r0 as u8.private;
    input r1 as u8.private;
    add.w r0 r1 into r2;
    output r2 as u8.private;

function addw_u16:
    input r0 as u16.private;
    input r1 as u16.private;
    add.w r0 r1 into r2;
    output r2 as u16.private;

function addw_u32:
    input r0 as u32.private;
    input r1 as u32.private;
    add.w r0 r1 into r2;
    output r2 as u32.private;

function addw_u64:
    input r0 as u64.private;
    input r1 as u64.private;
    add.w r0 r1 into r2;
    output r2 as u64.private;

function addw_u128:
    input r0 as u128.private;
    input r1 as u128.private;
    add.w r0 r1 into r2;
    output r2 as u128.private;
