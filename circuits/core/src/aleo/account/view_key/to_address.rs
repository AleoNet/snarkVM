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

impl<A: Aleo> ViewKey<A> {
    /// Returns the account address for this account view key.
    pub fn to_address(&self) -> Address<A> {
        Address::from_group(A::g_scalar_multiply(&self.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aleo::{account::from_private_key::tests::generate_private_and_compute_key, Devnet as Circuit};
    use snarkvm_algorithms::SignatureSchemeOperations;
    use snarkvm_curves::ProjectiveCurve;

    const ITERATIONS: u64 = 100;

    pub(crate) fn generate_view_key_and_address()
    -> (<Circuit as Environment>::ScalarField, <Circuit as Environment>::Affine) {
        // Compute the signature parameters.
        let native = Circuit::native_signature_scheme();
        // Generate the private key and compute key components.
        let (sk_sig, r_sig, _, _, sk_prf) = generate_private_and_compute_key();
        // Compute the account view key.
        let view_key = sk_sig + r_sig + sk_prf;
        // Compute the account address.
        let address = native.g_scalar_multiply(&view_key);
        // Return the view key and address.
        (view_key, address.to_affine())
    }

    fn check_to_address(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        for i in 0..ITERATIONS {
            // Generate the view key and address.
            let (view_key, address) = generate_view_key_and_address();

            // Initialize the view key.
            let candidate = ViewKey::<Circuit>::new(mode, view_key);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = candidate.to_address();
                assert_eq!(address, candidate.to_group().eject_value());

                // TODO (howardwu): Resolve skipping the cost count checks for the burn-in round.
                if i > 0 {
                    assert_scope!(<=num_constants, num_public, num_private, num_constraints);
                }
            });
        }
    }

    #[test]
    fn test_to_address_constant() {
        check_to_address(Mode::Constant, 1000, 0, 0, 0);
    }

    #[test]
    fn test_to_address_public() {
        check_to_address(Mode::Public, 500, 0, 1250, 1250);
    }

    #[test]
    fn test_to_address_private() {
        check_to_address(Mode::Private, 500, 0, 1250, 1250);
    }
}
