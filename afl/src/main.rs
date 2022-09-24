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

#[macro_use]
extern crate afl;

use snarkvm::{compiler::Program, console::network::Testnet3, prelude::test_crypto_rng, VM};

type CurrentNetwork = Testnet3;

fn main() {
    fuzz!(|program: Program<CurrentNetwork>| {
        // Initialize the VM.
        if let Ok(vm) = VM::<CurrentNetwork>::new() {
            // Initialize the RNG.
            let rng = &mut test_crypto_rng();

            // Deploy.
            if let Ok(transaction) = vm.deploy(&program, rng) {
                // Verify.
                vm.verify(&transaction);
            }
        }
    });
}
