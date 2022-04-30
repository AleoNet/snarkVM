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

impl<A: Aleo> ComputeKey<A> {
    /// Returns the account compute key for this account private key.
    pub fn from_private_key(private_key: &PrivateKey<A>) -> Self {
        // Extract (sk_sig, r_sig).
        let (sk_sig, r_sig) = (private_key.sk_sig(), private_key.r_sig());

        // Compute G^sk_sig.
        let pk_sig = A::g_scalar_multiply(sk_sig);

        // Compute G^r_sig.
        let pr_sig = A::g_scalar_multiply(r_sig);

        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf = A::hash_to_scalar(&[pk_sig.to_x_coordinate(), pr_sig.to_x_coordinate()]);

        // Return the compute key.
        Self { pk_sig, pr_sig, sk_prf }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::Devnet as Circuit;
    use snarkvm_algorithms::SignatureSchemeOperations;
    use snarkvm_curves::ProjectiveCurve;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 100;

    #[allow(clippy::type_complexity)]
    pub(crate) fn generate_private_and_compute_key() -> (
        <Circuit as Environment>::ScalarField,
        <Circuit as Environment>::ScalarField,
        <Circuit as Environment>::Affine,
        <Circuit as Environment>::Affine,
        <Circuit as Environment>::ScalarField,
    ) {
        // Compute the signature parameters.
        let native = Circuit::native_signature_scheme();

        // Sample a random private key.
        let rng = &mut test_rng();
        let sk_sig: <Circuit as Environment>::ScalarField = UniformRand::rand(rng);
        let r_sig: <Circuit as Environment>::ScalarField = UniformRand::rand(rng);

        // Compute G^sk_sig.
        let pk_sig = native.g_scalar_multiply(&sk_sig).to_affine();
        // Compute G^r_sig.
        let pr_sig = native.g_scalar_multiply(&r_sig).to_affine();
        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf = native.hash_to_scalar_field(&[pk_sig.x, pr_sig.x]);

        // Return the private key and compute key components.
        (sk_sig, r_sig, pk_sig, pr_sig, sk_prf)
    }

    fn check_from_private_key(
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
            let private_key = PrivateKey::<Circuit>::new(mode, (sk_sig, r_sig));

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = ComputeKey::from_private_key(&private_key);
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
    fn test_from_private_key_constant() {
        check_from_private_key(Mode::Constant, 2261, 0, 0, 0);
    }

    #[test]
    fn test_from_private_key_public() {
        check_from_private_key(Mode::Public, 1008, 0, 3093, 3094);
    }

    #[test]
    fn test_from_private_key_private() {
        check_from_private_key(Mode::Private, 1008, 0, 3093, 3094);
    }
}
