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

use super::*;

impl<A: Aleo> PrivateKey<A> {
    /// Returns the account compute key for this account private key.
    pub fn to_compute_key(&self) -> ComputeKey<A> {
        ComputeKey::from_private_key(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{account::from_private_key::tests::generate_private_and_compute_key, Devnet as Circuit};

    const ITERATIONS: usize = 100;

    fn check_to_compute_key(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        for i in 0..ITERATIONS {
            // Generate the private key and compute key components.
            let (sk_sig, r_sig, pk_sig, pr_sig, sk_prf) = generate_private_and_compute_key();

            // Initialize the private key.
            let candidate = PrivateKey::<Circuit>::new(mode, (sk_sig, r_sig));

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = candidate.to_compute_key();
                assert_eq!(pk_sig, candidate.pk_sig().eject_value());
                assert_eq!(pr_sig, candidate.pr_sig().eject_value());
                assert_eq!(sk_prf, candidate.sk_prf().eject_value());

                // TODO (howardwu): Resolve skipping the cost count checks for the burn-in round.
                if i > 0 {
                    assert_scope!(num_constants, num_public, num_private, num_constraints);
                }
            });
        }
    }

    #[test]
    fn test_to_compute_key_constant() {
        check_to_compute_key(Mode::Constant, 2261, 0, 0, 0);
    }

    #[test]
    fn test_to_compute_key_public() {
        check_to_compute_key(Mode::Public, 1008, 0, 3093, 3094);
    }

    #[test]
    fn test_to_compute_key_private() {
        check_to_compute_key(Mode::Private, 1008, 0, 3093, 3094);
    }
}
