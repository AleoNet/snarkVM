/*
randomness: 78952092
cases:
  - program: pass_in_data.aleo
    function: test_data_is_equal
    inputs: [data1dpjkcmr049vt4z, data1wahhymry9kmx0s]
  - program: pass_in_data.aleo
    function: test_data_is_equal
    inputs: [data1qa, data1qc]
  - program: pass_in_data.aleo
    function: test_data_is_equal_to_literal
    inputs: [data1qa]
  - program: pass_in_data.aleo
    function: test_data_is_equal_to_literal
    inputs: [data1qa]
*/

program pass_in_data.aleo;

function test_data_is_equal:
    input r0 as $DATA[1u32].private;
    input r1 as $DATA[1u32].private;
    is.eq r0 r1 into r2;
    is.neq r0 r1 into r3;
    output r2 as boolean.private;
    output r3 as boolean.private;

function test_data_is_equal_to_literal:
    input r0 as $DATA[1u32].private;
    is.eq r0 data1qa into r2;
    is.neq r0 data1qa into r3;
    output r2 as boolean.private;
    output r3 as boolean.private;

