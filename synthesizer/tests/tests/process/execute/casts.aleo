/*
randomness: 808
cases:
  - program: casts.aleo
    function: test_cast
    inputs: [0group]
  - program: casts.aleo
    function: test_cast
    inputs: [2group]
  - program: casts.aleo
    function: test_cast
    inputs: [89363714989903307245735717098563574705733591463163614225748337416674727625843187853442697973404985688481508350822group]
*/

program casts.aleo;

function test_cast:
    input r0 as group.private;
    cast r0 into r1 as group.y;
    cast r0 into r2 as group.x;
    cast r0 into r3 as field;
    assert.eq r2 r3;
    output r1 as field.private;
    output r2 as field.private;
