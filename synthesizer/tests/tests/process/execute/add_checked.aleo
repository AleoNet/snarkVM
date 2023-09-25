/*

randomness: 0

cases:

  - function: add_checked_i8
    inputs: [6i8, 9i8]
  - function: add_checked_i8
    inputs: [-100i8, -10i8]
  - function: add_checked_i8
    inputs: [0i8, 0i8]
  - function: add_checked_i8
    inputs: [50i8, -40i8]
  - function: add_checked_i8
    inputs: [-70i8, 30i8]
  - function: add_checked_i8
    inputs: [120i8, 50i8]

  - function: add_checked_i16
    inputs: [10000i16, 20000i16]
  - function: add_checked_i16
    inputs: [-10000i16, -20000i16]
  - function: add_checked_i16
    inputs: [10000i16, -20000i16]
  - function: add_checked_i16
    inputs: [-10000i16, 20000i16]
  - function: add_checked_i16
    inputs: [-20000i16, -20000i16]

  - function: add_checked_i32
    inputs: [10000000i32, 20000000i32]
  - function: add_checked_i32
    inputs: [-10000000i32, -20000000i32]
  - function: add_checked_i32
    inputs: [10000000i32, -20000000i32]
  - function: add_checked_i32
    inputs: [-10000000i32, 20000000i32]
  - function: add_checked_i32
    inputs: [2000000000i32, 2000000000i32]

  - function: add_checked_i64
    inputs: [10000000000000i64, 20000000000000i64]
  - function: add_checked_i64
    inputs: [-10000000000000i64, -20000000000000i64]
  - function: add_checked_i64
    inputs: [10000000000000i64, -20000000000000i64]
  - function: add_checked_i64
    inputs: [-10000000000000i64, 20000000000000i64]
  - function: add_checked_i64
    inputs: [9000000000000000000i64, 8000000000000000000i64]

  - function: add_checked_i128
    inputs: [10000000000000000000000i128, 20000000000000000000000i128]
  - function: add_checked_i128
    inputs: [-10000000000000000000000i128, -20000000000000000000000i128]
  - function: add_checked_i128
    inputs: [10000000000000000000000i128, -20000000000000000000000i128]
  - function: add_checked_i128
    inputs: [-10000000000000000000000i128, 20000000000000000000000i128]
  - function: add_checked_i128
    inputs: [85070591730234615865843651857942052864i128, 85070591730234615865843651857942052864i128]

  - function: add_checked_u8
    inputs: [6u8, 9u8]
  - function: add_checked_u8
    inputs: [100u8, 120u8]
  - function: add_checked_u8
    inputs: [0u8, 0u8]
  - function: add_checked_u8
    inputs: [120u8, 200u8]

  - function: add_checked_u16
    inputs: [10000u16, 20000u16]
  - function: add_checked_u16
    inputs: [30000u16, 20000u16]
  - function: add_checked_u16
    inputs: [40000u16, 40000u16]

  - function: add_checked_u32
    inputs: [10000000u32, 20000000u32]
  - function: add_checked_u32
    inputs: [2500000000u32, 1500000000u32]
  - function: add_checked_u32
    inputs: [3000000000u32, 2000000000u32]

  - function: add_checked_u64
    inputs: [10000000000000u64, 20000000000000u64]
  - function: add_checked_u64
    inputs: [7000000000000000000u64, 10000000000000000000u64]
  - function: add_checked_u64
    inputs: [10000000000000000000u64, 9000000000000000000u64]

  - function: add_checked_u128
    inputs: [10000000000000000000000u128, 20000000000000000000000u128]
  - function: add_checked_u128
    inputs: [200000000000000000000000000000000000000u128, 100000000000000000000000000000000000000u128]
  - function: add_checked_u128
    inputs: [200000000000000000000000000000000000000u128, 200000000000000000000000000000000000000u128]

  - function: add_checked_field
    inputs: [8field, 88field]
  - function: add_checked_field
    inputs: [-1field, 0field]
  - function: add_checked_field
    inputs: [8444461749428370424248824938781546531375899335154063827935233455917409239040field, 1field]
  - function: add_checked_field
    inputs: [8444461749428370424248824938781546531375899335154063827935233455917409239040field, 3field]
  - function: add_checked_field
    inputs: [111118444461749428370424248824938781546531375899335154063827935233455917409239040field, 10field]

  - function: add_checked_group
    inputs: [0group, 7810607721416582242904415504650443951498042435501746664987470571546413371306group]
  - function: add_checked_group
    inputs: [7810607721416582242904415504650443951498042435501746664987470571546413371306group, 7810607721416582242904415504650443951498042435501746664987470571546413371306group]
  - function: add_checked_group
    inputs: [2group, 2group]

  - function: add_checked_scalar
    inputs: [8scalar, 88scalar]
  - function: add_checked_scalar
    inputs: [0scalar, -1scalar]
  - function: add_checked_scalar
    inputs: [1scalar, 2111115437357092606062206234695386632838870926408408195193685246394721360382scalar]
  - function: add_checked_scalar
    inputs: [11scalar, 2111115437357092606062206234695386632838870926408408195193685246394721360382scalar]
  - function: add_checked_scalar
    inputs: [11111scalar, 999999992111115437357092606062206234695386632838870926408408195193685246394721360382scalar]
*/

program add_checked.aleo;

function add_checked_i8:
    input r0 as i8.private;
    input r1 as i8.private;
    add r0 r1 into r2;
    output r2 as i8.private;

function add_checked_i16:
    input r0 as i16.private;
    input r1 as i16.private;
    add r0 r1 into r2;
    output r2 as i16.private;

function add_checked_i32:
    input r0 as i32.private;
    input r1 as i32.private;
    add r0 r1 into r2;
    output r2 as i32.private;

function add_checked_i64:
    input r0 as i64.private;
    input r1 as i64.private;
    add r0 r1 into r2;
    output r2 as i64.private;

function add_checked_i128:
    input r0 as i128.private;
    input r1 as i128.private;
    add r0 r1 into r2;
    output r2 as i128.private;

function add_checked_u8:
    input r0 as u8.private;
    input r1 as u8.private;
    add r0 r1 into r2;
    output r2 as u8.private;

function add_checked_u16:
    input r0 as u16.private;
    input r1 as u16.private;
    add r0 r1 into r2;
    output r2 as u16.private;

function add_checked_u32:
    input r0 as u32.private;
    input r1 as u32.private;
    add r0 r1 into r2;
    output r2 as u32.private;

function add_checked_u64:
    input r0 as u64.private;
    input r1 as u64.private;
    add r0 r1 into r2;
    output r2 as u64.private;

function add_checked_u128:
    input r0 as u128.private;
    input r1 as u128.private;
    add r0 r1 into r2;
    output r2 as u128.private;

function add_checked_field:
    input r0 as field.private;
    input r1 as field.private;
    add r0 r1 into r2;
    output r2 as field.private;

function add_checked_group:
    input r0 as group.private;
    input r1 as group.private;
    add r0 r1 into r2;
    output r2 as group.private;

function add_checked_scalar:
    input r0 as scalar.private;
    input r1 as scalar.private;
    add r0 r1 into r2;
    output r2 as scalar.private;
