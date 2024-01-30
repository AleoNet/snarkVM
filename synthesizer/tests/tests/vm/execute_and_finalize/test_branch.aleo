/*
randomness: 98372
cases:
  - program: test_branch.aleo
    function: basic_branch
    inputs: [1u8, 1u8]
  - program: test_branch.aleo
    function: basic_branch
    inputs: [0u8, 1u8]
  - program: test_branch.aleo
    function: basic_branch
    inputs: [0u8, 0u8]
  - program: test_branch.aleo
    function: initialize_data
    inputs: ["[0u8, 1u8, 2u8]", "[1u8, 2u8, 3u8]"]
  - program: test_branch.aleo
    function: branch_with_mapping
    inputs: [true]
  - program: test_branch.aleo
    function: branch_with_mapping
    inputs: [false]

*/

program test_branch.aleo;

mapping data:
    key as u8.public;
    value as u8.public;

function basic_branch:
    input r0 as u8.public;
    input r1 as u8.public;
    async basic_branch r0 r1 into r2;
    output r2 as test_branch.aleo/basic_branch.future;

finalize basic_branch:
    input r0 as u8.public;
    input r1 as u8.public;
    branch.eq r0 0u8 to exit_one;
    assert.eq true false;
    position exit_one;
    branch.neq r1 1u8 to exit_two;
    assert.eq true false;
    position exit_two;

function initialize_data:
    input r0 as [u8; 3u32].public;
    input r1 as [u8; 3u32].public;
    async initialize_data r0 r1 into r2;
    output r2 as test_branch.aleo/initialize_data.future;

finalize initialize_data:
    input r0 as [u8; 3u32].public;
    input r1 as [u8; 3u32].public;
    set r1[0u32] into data[r0[0u32]];
    set r1[1u32] into data[r0[1u32]];
    set r1[2u32] into data[r0[2u32]];

function branch_with_mapping:
    input r0 as boolean.public;
    async branch_with_mapping r0 into r1;
    output r1 as test_branch.aleo/branch_with_mapping.future;

finalize branch_with_mapping:
    input r0 as boolean.public;

    branch.eq r0 true to exit_one;
    get data[0u8] into r1;
    branch.eq true true to exit_two;
    position exit_one;
    get data[1u8] into r1;
    position exit_two;

    get data[2u8] into r2;
    add r1 r2 into r6;
    set r6 into data[2u8];





