/*

randomness: 0

cases:

  - function: and_i8
    inputs: [0i8, -113i8]
  - function: and_i8
    inputs: [107i8, 0i8]
  - function: and_i8
    inputs: [-1i8, -113i8]
  - function: and_i8
    inputs: [87i8, -1i8]
  - function: and_i8
    inputs: [15i8, -16i8]
  - function: and_i8
    inputs: [31i8, -8i8]
  - function: and_i8
    inputs: [-70i8, 30i8]

  - function: and_i16
    inputs: [0i16, 20000i16]
  - function: and_i16
    inputs: [-13000i16, 0i16]
  - function: and_i16
    inputs: [-1i16, 20000i16]
  - function: and_i16
    inputs: [-13000i16, -1i16]
  - function: and_i16
    inputs: [-256i16, 255i16]
  - function: and_i16
    inputs: [-128i16, 511i16]
  - function: and_i16
    inputs: [-10000i16, 20000i16]

  - function: and_i32
    inputs: [0i32, 20000000i32]
  - function: and_i32
    inputs: [-21000000i32, 0i32]
  - function: and_i32
    inputs: [-1i32, 30888000i32]
  - function: and_i32
    inputs: [-21000000i32, -1i32]
  - function: and_i32
    inputs: [-65536i32, 65535i32]
  - function: and_i32
    inputs: [-32768i32, 131071i32]
  - function: and_i32
    inputs: [-10000000i32, 20000000i32]

  - function: and_i64
    inputs: [0i64, 20038000000000i64]
  - function: and_i64
    inputs: [-20000000000011i64, 0i64]
  - function: and_i64
    inputs: [-1i64, 20000000000000i64]
  - function: and_i64
    inputs: [-20000000000011i64, -1i64]
  - function: and_i64
    inputs: [-4294967296i64, 4294967295i64]
  - function: and_i64
    inputs: [-2147483648i64, 8589934591i64]
  - function: and_i64
    inputs: [9000000000000000000i64, 8000000000000000000i64]

  - function: and_i128
    inputs: [0i128, 20000000000000000777000i128]
  - function: and_i128
    inputs: [-18000050000500000000000i128, 0i128]
  - function: and_i128
    inputs: [-1i128, 20000000000000000777000i128]
  - function: and_i128
    inputs: [-18000050000500000000000i128, -1i128]
  - function: and_i128
    inputs: [-18446744073709551616i128, 4294967295i128]
  - function: and_i128
    inputs: [-9223372036854775808i128, 8589934591i128]
  - function: and_i128
    inputs: [85070591730234615865843651857942052864i128, 85070591730234615865843651857942052864i128]

  - function: and_u8
    inputs: [0u8, 209u8]
  - function: and_u8
    inputs: [5u8, 0u8]
  - function: and_u8
    inputs: [255u8, 209u8]
  - function: and_u8
    inputs: [5u8, 255u8]
  - function: and_u8
    inputs: [15u8, 240u8]
  - function: and_u8
    inputs: [31u8, 248u8]
  - function: and_u8
    inputs: [125u8, 98u8]

  - function: and_u16
    inputs: [0u16, 20000u16]
  - function: and_u16
    inputs: [10000u16, 0u16]
  - function: and_u16
    inputs: [65535u16, 20000u16]
  - function: and_u16
    inputs: [10000u16, 65535u16]
  - function: and_u16
    inputs: [65280u16, 255u16]
  - function: and_u16
    inputs: [65408u16, 511u16]
  - function: and_u16
    inputs: [30000u16, 20000u16]

  - function: and_u32
    inputs: [0u32, 20000000u32]
  - function: and_u32
    inputs: [10000000u32, 0u32]
  - function: and_u32
    inputs: [4294967295u32, 20000000u32]
  - function: and_u32
    inputs: [10000000u32, 4294967295u32]
  - function: and_u32
    inputs: [4294901760u32, 65535u32]
  - function: and_u32
    inputs: [4294934528u32, 131071u32]
  - function: and_u32
    inputs: [2500000000u32, 1500000000u32]

  - function: and_u64
    inputs: [0u64, 20000000000000u64]
  - function: and_u64
    inputs: [10000000000000000000u64, 0u64]
  - function: and_u64
    inputs: [18446744073709551615u64, 20000000000000u64]
  - function: and_u64
    inputs: [10000000000000000000u64, 18446744073709551615u64]
  - function: and_u64
    inputs: [18446744069414584320u64, 4294967295u64]
  - function: and_u64
    inputs: [18446744071562067968u64, 8589934591u64]
  - function: and_u64
    inputs: [10000000000000000000u64, 9000000000000000000u64]

  - function: and_u128
    inputs: [0u128, 20000000000000000000000u128]
  - function: and_u128
    inputs: [10000000000000000000000u128, 0u128]
  - function: and_u128
    inputs: [340282366920938463463374607431768211455u128, 20000000000000000000000u128]
  - function: and_u128
    inputs: [10000000000000000000000u128, 340282366920938463463374607431768211455u128]
  - function: and_u128
    inputs: [340282366920938463444927863358058659840u128, 18446744073709551615u128]
  - function: and_u128
    inputs: [340282366920938463454151235394913435648u128, 36893488147419103231u128]
  - function: and_u128
    inputs: [200000000000000000000000000000000000000u128, 100000000000000000000000000000000000000u128]
*/

program and.aleo;

function and_i8:
    input r0 as i8.private;
    input r1 as i8.private;
    and r0 r1 into r2;
    output r2 as i8.private;

function and_i16:
    input r0 as i16.private;
    input r1 as i16.private;
    and r0 r1 into r2;
    output r2 as i16.private;

function and_i32:
    input r0 as i32.private;
    input r1 as i32.private;
    and r0 r1 into r2;
    output r2 as i32.private;

function and_i64:
    input r0 as i64.private;
    input r1 as i64.private;
    and r0 r1 into r2;
    output r2 as i64.private;

function and_i128:
    input r0 as i128.private;
    input r1 as i128.private;
    and r0 r1 into r2;
    output r2 as i128.private;

function and_u8:
    input r0 as u8.private;
    input r1 as u8.private;
    and r0 r1 into r2;
    output r2 as u8.private;

function and_u16:
    input r0 as u16.private;
    input r1 as u16.private;
    and r0 r1 into r2;
    output r2 as u16.private;

function and_u32:
    input r0 as u32.private;
    input r1 as u32.private;
    and r0 r1 into r2;
    output r2 as u32.private;

function and_u64:
    input r0 as u64.private;
    input r1 as u64.private;
    and r0 r1 into r2;
    output r2 as u64.private;

function and_u128:
    input r0 as u128.private;
    input r1 as u128.private;
    and r0 r1 into r2;
    output r2 as u128.private;
