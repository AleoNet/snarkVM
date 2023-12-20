/*
cases:
  - program: point_arithmetic.aleo
    function: add_map_add
    inputs:
      - "{ x: 1u8, y: 2u8 }"
      - "{ x: 3u8, y: 4u8 }"
      - "{ x: 5u8, y: 6u8, z: 7u8 }"
*/

program two_dimensional.aleo;

struct point:
    x as u8;
    y as u8;

function add_:
    input r0 as point.private;
    input r1 as point.private;
    add r0.x r1.x into r2;
    add r0.y r1.y into r3;
    cast r2 r3 into r4 as point;
    output r4 as point.private;

/////////////////////////////////////////////////

program three_dimensional.aleo;

struct point:
    x as u8;
    y as u8;
    z as u8;

function add_:
    input r0 as point.private;
    input r1 as point.private;
    add r0.x r1.x into r2;
    add r0.y r1.y into r3;
    add r0.z r1.z into r4;
    cast r2 r3 r4 into r5 as point;
    output r5 as point.private;

/////////////////////////////////////////////////

import two_dimensional.aleo;
import three_dimensional.aleo;

program point_arithmetic.aleo;

struct point:
    x as u8;
    y as u8;

struct three_dim_point:
    x as u8;
    y as u8;
    z as u8;

function add_map_add:
    input r0 as two_dimensional.aleo/point.private;
    input r1 as two_dimensional.aleo/point.private;
    input r2 as three_dimensional.aleo/point.private;
    call two_dimensional.aleo/add_ r0 r1 into r3;
    cast r3.x r3.y 0u8 into r4 as three_dimensional.aleo/point;
    call three_dimensional.aleo/add_ r2 r4 into r5;
    output r5 as three_dimensional.aleo/point.private;
