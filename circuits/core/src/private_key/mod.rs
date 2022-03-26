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

use snarkvm_circuits_environment::{traits::*, Environment};
use snarkvm_circuits_types::{Address, Boolean, I64};

pub struct PrivateKey<E: Environment> {}

impl<E: Environment> Inject for PrivateKey<E> {
    type Primitive = E::BaseField;

    /// Initializes an account private key from the given mode and account seed.
    fn new(mode: Mode, seed: &N::AccountSeed) -> PrivateKey<E> {
        // Construct the sk_sig domain separator.
        let sk_sig_input = ACCOUNT_SEED_SK_SIG_DOMAIN;
        let sk_sig_domain = N::ProgramScalarField::from_bytes_le_mod_order(sk_sig_input.as_bytes());

        // Construct the r_sig domain separator.
        let r_sig_input = format!("{}_{}", ACCOUNT_SEED_R_SIG_DOMAIN, 0);
        let r_sig_domain = N::ProgramScalarField::from_bytes_le_mod_order(r_sig_input.as_bytes());

        // Construct the preimage.
        let mut preimage = vec![*seed];
        preimage.push(F::from(input.len() as u128)); // Input length
        preimage.extend_from_slice(input);

        Self {
            sk_sig: N::AccountSeedPRF::evaluate(seed, &vec![sk_sig_domain])
                .expect("Failed to derive private key component for PRF(seed, sk_sig_domain)"),
            r_sig: N::AccountSeedPRF::evaluate(seed, &vec![r_sig_domain])
                .expect("Failed to derive private key component for PRF(seed, r_sig_domain)"),
        }
    }
}
