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

use snarkvm::{compiler::Program, console::network::Testnet3, prelude::test_crypto_rng};
use snarkvm::prelude::{PrivateKey, VM};
use std::sync::Once;
use once_cell::sync::OnceCell;
use snarkvm::circuit;
use snarkvm::circuit::Mode;
use crate::circuit::{AleoV0, Inject};

static INSTANCE: OnceCell<VM<FuzzNetwork>> = OnceCell::new();
pub type FuzzNetwork = Testnet3;

pub fn init_vm() -> &'static VM<FuzzNetwork> {
    INSTANCE.get_or_init(|| VM::<FuzzNetwork>::new().unwrap())
}

pub fn fuzz_program(program: Program<FuzzNetwork>) {
    let vm = init_vm();

    // Initialize the RNG.
    let rng = &mut test_crypto_rng();

    //let private_key = circuit::PrivateKey::<AleoV0>::new(Mode::Private, pkey);

    // Deploy.
/*    if let Ok(deployment) = vm.deploy(&program, rng) {
        vm.verify_deployment(&deployment);
    }
*/
    // Execute
/*    if let Some(f) = program.functions().first() {
        // Initialize the private key.
        let pkey = PrivateKey::new(rng).unwrap();

        if let Ok(auth) = vm.authorize(&pkey, program.id(), f.0.clone(), &[], rng) {
            vm.execute(auth, rng); // ignore unwrap
        } else {
            // ignore
        }
    }*/
}
