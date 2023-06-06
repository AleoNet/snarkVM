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

pub mod genesis;
pub use genesis::*;

pub mod powers;
pub use powers::*;

const REMOTE_URL: &str = "https://testnet3.parameters.aleo.org";

// Degrees
impl_local!(Degree15, "resources/", "powers-of-beta-15", "usrs");
impl_remote!(Degree16, REMOTE_URL, "resources/", "powers-of-beta-16", "usrs");
impl_remote!(Degree17, REMOTE_URL, "resources/", "powers-of-beta-17", "usrs");
impl_remote!(Degree18, REMOTE_URL, "resources/", "powers-of-beta-18", "usrs");
impl_remote!(Degree19, REMOTE_URL, "resources/", "powers-of-beta-19", "usrs");
impl_remote!(Degree20, REMOTE_URL, "resources/", "powers-of-beta-20", "usrs");
impl_remote!(Degree21, REMOTE_URL, "resources/", "powers-of-beta-21", "usrs");
impl_remote!(Degree22, REMOTE_URL, "resources/", "powers-of-beta-22", "usrs");
impl_remote!(Degree23, REMOTE_URL, "resources/", "powers-of-beta-23", "usrs");
impl_remote!(Degree24, REMOTE_URL, "resources/", "powers-of-beta-24", "usrs");
impl_remote!(Degree25, REMOTE_URL, "resources/", "powers-of-beta-25", "usrs");
impl_remote!(Degree26, REMOTE_URL, "resources/", "powers-of-beta-26", "usrs");
impl_remote!(Degree27, REMOTE_URL, "resources/", "powers-of-beta-27", "usrs");
impl_remote!(Degree28, REMOTE_URL, "resources/", "powers-of-beta-28", "usrs");

// Shifted Degrees
impl_local!(ShiftedDegree15, "resources/", "shifted-powers-of-beta-15", "usrs");
impl_remote!(ShiftedDegree16, REMOTE_URL, "resources/", "shifted-powers-of-beta-16", "usrs");
impl_remote!(ShiftedDegree17, REMOTE_URL, "resources/", "shifted-powers-of-beta-17", "usrs");
impl_remote!(ShiftedDegree18, REMOTE_URL, "resources/", "shifted-powers-of-beta-18", "usrs");
impl_remote!(ShiftedDegree19, REMOTE_URL, "resources/", "shifted-powers-of-beta-19", "usrs");
impl_remote!(ShiftedDegree20, REMOTE_URL, "resources/", "shifted-powers-of-beta-20", "usrs");
impl_remote!(ShiftedDegree21, REMOTE_URL, "resources/", "shifted-powers-of-beta-21", "usrs");
impl_remote!(ShiftedDegree22, REMOTE_URL, "resources/", "shifted-powers-of-beta-22", "usrs");
impl_remote!(ShiftedDegree23, REMOTE_URL, "resources/", "shifted-powers-of-beta-23", "usrs");
impl_remote!(ShiftedDegree24, REMOTE_URL, "resources/", "shifted-powers-of-beta-24", "usrs");
impl_remote!(ShiftedDegree25, REMOTE_URL, "resources/", "shifted-powers-of-beta-25", "usrs");
impl_remote!(ShiftedDegree26, REMOTE_URL, "resources/", "shifted-powers-of-beta-26", "usrs");
impl_remote!(ShiftedDegree27, REMOTE_URL, "resources/", "shifted-powers-of-beta-27", "usrs");

// Powers of Beta Times Gamma * G
impl_local!(Gamma, "resources/", "powers-of-beta-gamma", "usrs");
// Negative Powers of Beta in G2
impl_local!(NegBeta, "resources/", "neg-powers-of-beta", "usrs");
// Negative Powers of Beta in G2
impl_local!(BetaH, "resources/", "beta-h", "usrs");

// Mint
impl_remote!(MintProver, REMOTE_URL, "resources/", "mint", "prover");
impl_remote!(MintVerifier, REMOTE_URL, "resources/", "mint", "verifier");
// TransferPrivate
impl_remote!(TransferPrivateProver, REMOTE_URL, "resources/", "transfer_private", "prover");
impl_remote!(TransferPrivateVerifier, REMOTE_URL, "resources/", "transfer_private", "verifier");
// TransferPublic
impl_remote!(TransferPublicProver, REMOTE_URL, "resources/", "transfer_public", "prover");
impl_remote!(TransferPublicVerifier, REMOTE_URL, "resources/", "transfer_public", "verifier");
// TransferPrivateToPublic
impl_remote!(TransferPrivateToPublicProver, REMOTE_URL, "resources/", "transfer_private_to_public", "prover");
impl_remote!(TransferPrivateToPublicVerifier, REMOTE_URL, "resources/", "transfer_private_to_public", "verifier");
// TransferPublicToPrivate
impl_remote!(TransferPublicToPrivateProver, REMOTE_URL, "resources/", "transfer_public_to_private", "prover");
impl_remote!(TransferPublicToPrivateVerifier, REMOTE_URL, "resources/", "transfer_public_to_private", "verifier");
// Join
impl_remote!(JoinProver, REMOTE_URL, "resources/", "join", "prover");
impl_remote!(JoinVerifier, REMOTE_URL, "resources/", "join", "verifier");
// Split
impl_remote!(SplitProver, REMOTE_URL, "resources/", "split", "prover");
impl_remote!(SplitVerifier, REMOTE_URL, "resources/", "split", "verifier");
// Fee
impl_remote!(FeeProver, REMOTE_URL, "resources/", "fee", "prover");
impl_remote!(FeeVerifier, REMOTE_URL, "resources/", "fee", "verifier");

#[macro_export]
macro_rules! insert_credit_keys {
    ($map:ident, $type:ident<$network:ident>, $variant:ident) => {{
        paste::paste! {
            let string = stringify!([<$variant:lower>]);
            $crate::insert_key!($map, string, $type<$network>, ("mint", $crate::testnet3::[<Mint $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("transfer_private", $crate::testnet3::[<TransferPrivate $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("transfer_public", $crate::testnet3::[<TransferPublic $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("transfer_private_to_public", $crate::testnet3::[<TransferPrivateToPublic $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("transfer_public_to_private", $crate::testnet3::[<TransferPublicToPrivate $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("join", $crate::testnet3::[<Join $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("split", $crate::testnet3::[<Split $variant>]::load_bytes()));
            $crate::insert_key!($map, string, $type<$network>, ("fee", $crate::testnet3::[<Fee $variant>]::load_bytes()));
        }
    }};
}

#[macro_export]
macro_rules! insert_key {
    ($map:ident, $string:tt, $type:ident<$network:ident>, ($name:tt, $circuit_key:expr)) => {{
        // Load the circuit key bytes.
        let key_bytes: Vec<u8> = $circuit_key.expect(&format!("Failed to load {} bytes", $string));
        // Recover the circuit key.
        let key = $type::<$network>::from_bytes_le(&key_bytes[1..]).expect(&format!("Failed to recover {}", $string));
        // Insert the circuit key.
        $map.insert($name.to_string(), std::sync::Arc::new(key));
    }};
}

// Inclusion
impl_remote!(InclusionProver, REMOTE_URL, "resources/", "inclusion", "prover");
impl_remote!(InclusionVerifier, REMOTE_URL, "resources/", "inclusion", "verifier");

/// The function name for the inclusion circuit.
pub const TESTNET3_INCLUSION_FUNCTION_NAME: &str = "inclusion";

lazy_static! {
    pub static ref INCLUSION_PROVING_KEY: Vec<u8> =
        InclusionProver::load_bytes().expect("Failed to load inclusion proving key");
    pub static ref INCLUSION_VERIFYING_KEY: Vec<u8> =
        InclusionVerifier::load_bytes().expect("Failed to load inclusion verifying key");
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_bindgen_test::*;
    wasm_bindgen_test_configure!(run_in_browser);

    #[wasm_bindgen_test]
    fn test_transfer_flow() {
        Degree16::load_bytes().expect("Failed to load degree 16");
        Degree17::load_bytes().expect("Failed to load degree 17");
        Degree18::load_bytes().expect("Failed to load degree 18");
        Degree19::load_bytes().expect("Failed to load degree 19");
        TransferPrivateVerifier::load_bytes().expect("Failed to load transfer_private verifier");
        TransferPublicVerifier::load_bytes().expect("Failed to load transfer_public verifier");
        TransferPrivateToPublicVerifier::load_bytes().expect("Failed to load transfer_private_to_public verifier");
        TransferPublicToPrivateVerifier::load_bytes().expect("Failed to load transfer_public_to_private verifier");
        FeeProver::load_bytes().expect("Failed to load fee prover");
        FeeVerifier::load_bytes().expect("Failed to load fee verifier");
        InclusionProver::load_bytes().expect("Failed to load inclusion prover");
        InclusionVerifier::load_bytes().expect("Failed to load inclusion verifier");
    }
}
