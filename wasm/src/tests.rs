// Copyright (C) 2019-2022 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use snarkvm_dpc::{testnet2::Testnet2, Account, Address, PrivateKey, ViewKey};
use snarkvm_utilities::ToBits;

use core::str::FromStr;
use wasm_bindgen_test::*;

const ITERATIONS: usize = 1000;

#[wasm_bindgen_test]
fn test_account() {
    const ALEO_TESTNET2_PRIVATE_KEY: &str = "APrivateKey1zkp8cC4jgHEBnbtu3xxs1Ndja2EMizcvTRDq5Nikdkukg1p";
    const ALEO_TESTNET2_VIEW_KEY: &str = "AViewKey1iAf6a7fv6ELA4ECwAth1hDNUJJNNoWNThmREjpybqder";
    const ALEO_TESTNET2_ADDRESS: &str = "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah";

    let private_key = PrivateKey::<Testnet2>::from_str(ALEO_TESTNET2_PRIVATE_KEY).unwrap();
    assert_eq!(ALEO_TESTNET2_PRIVATE_KEY, private_key.to_string());

    let view_key = ViewKey::from(&private_key);
    assert_eq!(ALEO_TESTNET2_VIEW_KEY, view_key.to_string());

    let address = Address::from(&view_key);
    assert_eq!(ALEO_TESTNET2_ADDRESS, address.to_string());
}

#[wasm_bindgen_test]
fn test_account_sign() {
    for _ in 0..ITERATIONS {
        // Sample a new account.
        let rng = &mut rand::thread_rng();
        let account = Account::<Testnet2>::new(rng);

        // Sign a message with the account private key.
        let result = account.private_key().sign(&b"hello world!".to_bits_le(), rng);
        assert!(result.is_ok(), "Failed to generate a signature");

        // Verify the signed message.
        let signature = result.unwrap();
        let result = account.address().verify_signature(&b"hello world!".to_bits_le(), &signature);
        assert!(result.is_ok(), "Failed to execute signature verification");
        assert!(result.unwrap(), "Signature is invalid");
    }
}
