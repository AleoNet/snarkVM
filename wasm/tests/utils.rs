// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use snarkvm_wasm::{
    circuit::AleoV0,
    console::{
        account::PrivateKey,
        network::Testnet3,
        program::{Identifier, Response},
    },
    synthesizer::{Process, Program, Trace},
    utilities::TestRng,
};

use std::str::FromStr;

pub fn execute_hello_program(process: &mut Process<Testnet3>) -> (Response<Testnet3>, Trace<Testnet3>) {
    let hello = Program::from_str("program hello_hello.aleo;\n\nfunction hello:\n    input r0 as u32.public;\n    input r1 as u32.private;\n    add r0 r1 into r2;\n    output r2 as u32.private;\n").unwrap();
    let function_name = Identifier::from_str("hello").unwrap();
    let mut rng = TestRng::default();
    let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
    process.add_program(&hello).unwrap();
    let authorization = process
        .authorize::<AleoV0, _>(&private_key, hello.id(), function_name, ["5u32", "5u32"].into_iter(), &mut rng)
        .unwrap();
    let (response, trace) = process.execute::<AleoV0>(authorization).unwrap();
    assert_eq!(&response.outputs()[0].to_string(), "10u32");
    (response, trace)
}
