/*
cases:
  - program: points.aleo
    function: add_
    inputs:
      - "{ x: 1u8, y: 2u8 }"
      - "{ x: 3u8, y: 4u8 }"
  - program: point_arithmetic.aleo
    function: add_two_points
    inputs:
      - "{ x: 1u8, y: 2u8 }"
      - "{ x: 3u8, y: 4u8 }"
*/

program points.aleo;

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

import points.aleo;

program point_arithmetic.aleo;

struct foo:
    x as u8;
    y as u8;

function add_two_points:
    input r0 as foo.private;
    input r1 as points.aleo/point.private;
    call points.aleo/add_ r0 r1 into r2;
    output r2 as points.aleo/point.private;
