/*

randomness: 0

cases:

  - function: addw_i8
    inputs: [6i8, 9i8]
  - function: addw_i8
    inputs: [-100i8, -10i8]
  - function: addw_i8
    inputs: [0i8, 0i8]
  - function: addw_i8
    inputs: [50i8, -40i8]
  - function: addw_i8
    inputs: [-70i8, 30i8]
  - function: addw_i8
    inputs: [120i8, 50i8]

  - function: addw_i16
    inputs: [10000i16, 20000i16]
  - function: addw_i16
    inputs: [-10000i16, -20000i16]
  - function: addw_i16
    inputs: [10000i16, -20000i16]
  - function: addw_i16
    inputs: [-10000i16, 20000i16]
  - function: addw_i16
    inputs: [-20000i16, -20000i16]

  - function: addw_i32
    inputs: [10000000i32, 20000000i32]
  - function: addw_i32
    inputs: [-10000000i32, -20000000i32]
  - function: addw_i32
    inputs: [10000000i32, -20000000i32]
  - function: addw_i32
    inputs: [-10000000i32, 20000000i32]
  - function: addw_i32
    inputs: [2000000000i32, 2000000000i32]

  - function: addw_i64
    inputs: [10000000000000i64, 20000000000000i64]
  - function: addw_i64
    inputs: [-10000000000000i64, -20000000000000i64]
  - function: addw_i64
    inputs: [10000000000000i64, -20000000000000i64]
  - function: addw_i64
    inputs: [-10000000000000i64, 20000000000000i64]
  - function: addw_i64
    inputs: [9000000000000000000i64, 8000000000000000000i64]

  - function: addw_i128
    inputs: [10000000000000000000000i128, 20000000000000000000000i128]
  - function: addw_i128
    inputs: [-10000000000000000000000i128, -20000000000000000000000i128]
  - function: addw_i128
    inputs: [10000000000000000000000i128, -20000000000000000000000i128]
  - function: addw_i128
    inputs: [-10000000000000000000000i128, 20000000000000000000000i128]
  - function: addw_i128
    inputs: [85070591730234615865843651857942052864i128, 85070591730234615865843651857942052864i128]

  - function: addw_u8
    inputs: [6u8, 9u8]
  - function: addw_u8
    inputs: [100u8, 120u8]
  - function: addw_u8
    inputs: [0u8, 0u8]
  - function: addw_u8
    inputs: [120u8, 200u8]

  - function: addw_u16
    inputs: [10000u16, 20000u16]
  - function: addw_u16
    inputs: [30000u16, 20000u16]
  - function: addw_u16
    inputs: [40000u16, 40000u16]

  - function: addw_u32
    inputs: [10000000u32, 20000000u32]
  - function: addw_u32
    inputs: [2500000000u32, 1500000000u32]
  - function: addw_u32
    inputs: [3000000000u32, 2000000000u32]

  - function: addw_u64
    inputs: [10000000000000u64, 20000000000000u64]
  - function: addw_u64
    inputs: [7000000000000000000u64, 10000000000000000000u64]
  - function: addw_u64
    inputs: [10000000000000000000u64, 9000000000000000000u64]

  - function: addw_u128
    inputs: [10000000000000000000000u128, 20000000000000000000000u128]
  - function: addw_u128
    inputs: [200000000000000000000000000000000000000u128, 100000000000000000000000000000000000000u128]
  - function: addw_u128
    inputs: [200000000000000000000000000000000000000u128, 200000000000000000000000000000000000000u128]

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
