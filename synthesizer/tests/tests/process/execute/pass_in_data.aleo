/*
randomness: 78952092
cases:
  - program: pass_in_data.aleo
    function: test_data_is_equal
    inputs: [data1dpjkcmr049vt4z, data1wahhymry9kmx0s]
  - program: pass_in_data.aleo
    function: test_data_is_equal
    inputs: [data1dpjkcmr049vt4z, data1dpjkcmr049vt4z]
  - program: pass_in_data.aleo
    function: test_data_is_equal_to_literal
    inputs: [data1wahhymry9kmx0s]
  - program: pass_in_data.aleo
    function: test_data_is_equal_to_literal
    inputs: [data1dpjkcmr0ypmk7unvvs2rhz3v]
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
    is.eq r0 data1dpjkcmr0ypmk7unvvs2rhz3v into r1;
    is.neq r0 data1dpjkcmr0ypmk7unvvs2rhz3v into r2;
    output r1 as boolean.private;
    output r2 as boolean.private;

