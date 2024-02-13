/*
randomness: 78952092
cases:
  - program: pass_in_data.aleo
    function: test_data_is_equal
    inputs: [data.]
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

program pass_in_data.aleo;

function test_data_is_equal:
    input r0 as data[1u32].private;
    input r1 as data[1u32].private;
    is.eq r0 r1 into r2;
    is.neq r0 r1 into r3;
