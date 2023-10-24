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

mod utils;
use utils::*;

use snarkvm_parameters::testnet3::{InclusionProver, NUM_POWERS_15, NUM_POWERS_18, NUM_POWERS_19, NUM_POWERS_28};
use snarkvm_wasm::{
    circuit::AleoV0,
    console::{
        account::{Address, PrivateKey, ViewKey},
        network::Testnet3,
    },
    ledger_query::Query,
    ledger_store::helpers::memory::BlockMemory,
    synthesizer::Process,
    utilities::TestRng,
};
use wasm_bindgen_test::*;

use core::str::FromStr;

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

async fn test_preload_powers_async() {
    // Pre-download powers.
    let mut process = Process::<Testnet3>::load_web().unwrap();
    process.universal_srs().preload_powers_async(16, 18).await.unwrap();

    // Requesting normal powers should not trigger any downloads.
    let powers_of_beta = process.universal_srs().powers_of_beta_g(0, NUM_POWERS_18).unwrap();
    assert_eq!(powers_of_beta.len(), NUM_POWERS_18);

    // Requesting powers of shifted powers should not trigger any downloads.
    let shifted_powers_of_beta =
        process.universal_srs().powers_of_beta_g(NUM_POWERS_28 - NUM_POWERS_18, NUM_POWERS_28 - NUM_POWERS_15).unwrap();
    assert_eq!(shifted_powers_of_beta.len(), NUM_POWERS_18 - NUM_POWERS_15);

    // Requesting powers of shifted powers should not trigger any downloads.
    execute_hello_program(&mut process);

    // Execute a program in wasm without triggering synchronous parameter downloads.
    assert!(process.get_proving_key("hello_hello.aleo", "hello").is_ok());

    // Attempt to extend the powers of beta again, only downloading the missing powers of 2^19.
    process.universal_srs().preload_powers_async(16, 19).await.unwrap();

    // Ensure the powers of beta exist and no downloads are triggered.
    let powers_of_beta = process.universal_srs().powers_of_beta_g(0, NUM_POWERS_19).unwrap();
    let shifted_powers_of_beta =
        process.universal_srs().powers_of_beta_g(NUM_POWERS_28 - NUM_POWERS_19, NUM_POWERS_28 - NUM_POWERS_15).unwrap();
    assert_eq!(powers_of_beta.len(), NUM_POWERS_19);
    assert_eq!(shifted_powers_of_beta.len(), NUM_POWERS_19 - NUM_POWERS_15);
}

#[test]
fn test_preload_powers_async_rust() {
    tokio_test::block_on(test_preload_powers_async());
}

#[wasm_bindgen_test]
async fn test_preload_powers_async_wasm() {
    test_preload_powers_async().await;
}

#[wasm_bindgen_test]
async fn test_async_inclusion_key_initialization() {
    let rng = &mut TestRng::default();

    // Download the inclusion prover using javascript fetch.
    Process::<Testnet3>::initialize_inclusion_prover_async().await.unwrap();

    // Ensure a program execution can be proven.
    let mut process = Process::load_web().unwrap();
    process.universal_srs().preload_powers_async(16, 17).await.unwrap();
    let (_, mut trace) = execute_hello_program(&mut process);
    let query = Query::<Testnet3, BlockMemory<Testnet3>>::from("https://api.explorer.aleo.org/v1");
    trace.prepare_async(query).await.unwrap();
    trace.prove_execution::<AleoV0, _>("hello_hello.aleo/hello", rng).unwrap();
}

#[wasm_bindgen_test]
async fn test_inclusion_key_insertion() {
    let rng = &mut TestRng::default();

    // Ensure the inclusion prover can't be initialized without the the correct bytes.
    let incorrect_length_result = Process::<Testnet3>::initialize_inclusion_prover_from_bytes(vec![5u8, 2u8]);
    let incorrect_bytes_result = Process::<Testnet3>::initialize_inclusion_prover_from_bytes(vec![5u8; 156031076]);
    assert!(incorrect_length_result.is_err());
    assert!(incorrect_bytes_result.is_err());

    // Ensure prover can be initialized with the correct bytes.
    let prover_bytes = InclusionProver::load_bytes_async().await.unwrap();
    Process::<Testnet3>::initialize_inclusion_prover_from_bytes(prover_bytes).unwrap();

    // Ensure once more that the inclusion prover can't be initialized without the the correct bytes.
    let incorrect_length_result = Process::<Testnet3>::initialize_inclusion_prover_from_bytes(vec![5u8, 2u8]);
    let incorrect_bytes_result = Process::<Testnet3>::initialize_inclusion_prover_from_bytes(vec![5u8; 156031076]);
    assert!(incorrect_length_result.is_err());
    assert!(incorrect_bytes_result.is_err());

    // Ensure a program execution can be proven after the inclusion key is inserted.
    let mut process = Process::load_web().unwrap();
    process.universal_srs().preload_powers_async(16, 17).await.unwrap();
    let (_, mut trace) = execute_hello_program(&mut process);
    let query = Query::<Testnet3, BlockMemory<Testnet3>>::from("https://api.explorer.aleo.org/v1");
    trace.prepare_async(query).await.unwrap();
    trace.prove_execution::<AleoV0, _>("hello_hello.aleo/hello", rng).unwrap();
}
