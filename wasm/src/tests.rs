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

const NUM_POWERS_15: usize = 1 << 15;
const NUM_POWERS_18: usize = 1 << 18;
const NUM_POWERS_19: usize = 1 << 19;
const NUM_POWERS_MAX: usize = 1 << 28;

use snarkvm_circuit_network::AleoV0;
use snarkvm_console::{
    account::{Address, PrivateKey, ViewKey},
    network::Testnet3,
    program::Identifier,
};
use snarkvm_synthesizer::{Process, Program};
use snarkvm_utilities::TestRng;

use core::str::FromStr;
use wasm_bindgen_test::*;

const ITERATIONS: usize = 1000;

#[wasm_bindgen_test]
fn test_account() {
    const ALEO_PRIVATE_KEY: &str = "APrivateKey1zkp8cC4jgHEBnbtu3xxs1Ndja2EMizcvTRDq5Nikdkukg1p";
    const ALEO_VIEW_KEY: &str = "AViewKey1n1n3ZbnVEtXVe3La2xWkUvY3EY7XaCG6RZJJ3tbvrrrD";
    const ALEO_ADDRESS: &str = "aleo1wvgwnqvy46qq0zemj0k6sfp3zv0mp77rw97khvwuhac05yuwscxqmfyhwf";

    let private_key = PrivateKey::<Testnet3>::from_str(ALEO_PRIVATE_KEY).unwrap();
    assert_eq!(ALEO_PRIVATE_KEY, private_key.to_string());

    let view_key = ViewKey::try_from(&private_key).unwrap();
    assert_eq!(ALEO_VIEW_KEY, view_key.to_string());

    let address = Address::try_from(&view_key).unwrap();
    assert_eq!(ALEO_ADDRESS, address.to_string());
}

#[wasm_bindgen_test]
fn test_account_sign() {
    let mut rng = TestRng::default();

    for _ in 0..ITERATIONS {
        // Sample a new private key and address.
        let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
        let address = Address::try_from(&private_key).unwrap();

        // Sign a message with the account private key.
        let result = private_key.sign_bytes("hello world!".as_bytes(), &mut rng);
        assert!(result.is_ok(), "Failed to generate a signature");

        // Verify the signed message.
        let signature = result.unwrap();
        let result = signature.verify_bytes(&address, "hello world!".as_bytes());
        assert!(result, "Failed to execute signature verification");
    }
}

#[wasm_bindgen_test]
async fn test_preload_powers_async() {
    // Pre-download powers.
    let mut process = Process::<Testnet3>::load_web().unwrap();
    process.universal_srs().preload_powers_async(16, 18).await.unwrap();

    // Requesting powers of beta normally should not trigger any downloads after pre-loading the powers.
    let powers_of_beta = process.universal_srs().powers_of_beta_g(0, NUM_POWERS_18).unwrap();
    assert_eq!(powers_of_beta.len(), NUM_POWERS_18);
    let shifted_powers_of_beta = process
        .universal_srs()
        .powers_of_beta_g(NUM_POWERS_MAX - NUM_POWERS_18, NUM_POWERS_MAX - NUM_POWERS_15)
        .unwrap();
    assert_eq!(shifted_powers_of_beta.len(), NUM_POWERS_18 - NUM_POWERS_15);

    // Execute a program in wasm without triggering synchronous parameter downloads.
    let hello = Program::from_str("program hello_hello.aleo;\n\nfunction hello:\n    input r0 as u32.public;\n    input r1 as u32.private;\n    add r0 r1 into r2;\n    output r2 as u32.private;\n").unwrap();
    process.add_program(&hello).unwrap();
    let function_name = Identifier::from_str("hello").unwrap();
    let mut rng = TestRng::default();
    let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
    let authorization = process
        .authorize::<AleoV0, _>(&private_key, hello.id(), function_name, ["5u32", "5u32"].into_iter(), &mut rng)
        .unwrap();

    // Assert no proving key exists prior to execution.
    assert!(process.get_proving_key(hello.id(), function_name).is_err());

    // Ensure the proving key is synthesized during execution and the outputs are correct.
    let (response, _) = process.execute::<AleoV0>(authorization).unwrap();
    assert!(process.get_proving_key(hello.id(), function_name).is_ok());
    assert_eq!(response.outputs()[0].to_string(), "10u32");

    // Attempt to extend the powers of beta again, only downloading the missing powers of 2^19.
    process.universal_srs().preload_powers_async(16, 19).await.unwrap();
    let powers_of_beta = process.universal_srs().powers_of_beta_g(0, NUM_POWERS_19).unwrap();
    let shifted_powers_of_beta = process
        .universal_srs()
        .powers_of_beta_g(NUM_POWERS_MAX - NUM_POWERS_19, NUM_POWERS_MAX - NUM_POWERS_15)
        .unwrap();

    // Ensure the powers of beta exist and no synchronous downloads are triggered.
    assert_eq!(powers_of_beta.len(), NUM_POWERS_19);
    assert_eq!(shifted_powers_of_beta.len(), NUM_POWERS_19 - NUM_POWERS_15);
}
