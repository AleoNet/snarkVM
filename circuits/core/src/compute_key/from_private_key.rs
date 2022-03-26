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
use crate::{PrivateKey};

impl<A: Account> ComputeKey<A> {
    /// Returns the account compute key for this account private key.
    pub fn from_private_key(private_key: &PrivateKey<A>) -> Self {
        // Extract (sk_sig, r_sig).
        let (sk_sig, r_sig) = (private_key.sk_sig(), private_key.r_sig());

        // Compute G^sk_sig.
        let pk_sig = A::g_scalar_multiply(sk_sig);

        // Compute G^r_sig.
        let pr_sig = A::g_scalar_multiply(r_sig);

        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf = A::hash_to_scalar(&[pk_sig.x, pr_sig.x]);

        // Return the compute key.
        Self { pk_sig, pr_sig, sk_prf }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Aleo;
    use snarkvm_algorithms::{signature::AleoSignatureScheme, SignatureScheme, SignatureSchemeOperations};
    use snarkvm_utilities::{test_rng, UniformRand};

    use rand::Rng;

    const ITERATIONS: usize = 100;

    fn check_from_private_key(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let mut rng = test_rng();

        for i in 0..ITERATIONS {
            // Sample random signature parameters.
            let setup_message: String = (0..(ITERATIONS + 1)).map(|_| rng.gen::<char>()).collect();
            let native = AleoSignatureScheme::<<Aleo as Environment>::AffineParameters>::setup(&setup_message);

            // Sample a random private key.
            let sk_sig: <Aleo as Environment>::ScalarField = UniformRand::rand(&mut test_rng());
            let r_sig: <Aleo as Environment>::ScalarField = UniformRand::rand(&mut test_rng());

            // Compute the expected output.
            let (pk_sig, pr_sig, sk_prf) = {
                // Compute G^sk_sig.
                let pk_sig = native.g_scalar_multiply(&sk_sig);
                // Compute G^r_sig.
                let pr_sig = native.g_scalar_multiply(&r_sig);
                // Compute sk_prf := RO(G^sk_sig || G^r_sig).
                let sk_prf = native.hash_to_scalar_field(&[pk_sig.x, pr_sig.x]);
                // Return the native compute key components.
                (pk_sig, pr_sig, sk_prf)
            };

            // Initialize the private key.
            let private_key = PrivateKey::<Aleo>::new(mode, (sk_sig, r_sig));

            Aleo::scope(&format!("{} {}", mode, i), || {
                let candidate = ComputeKey::from_private_key(&private_key);
                assert_eq!(pk_sig, candidate.pk_sig().eject_value());
                assert_eq!(pr_sig, candidate.pr_sig().eject_value());
                assert_eq!(sk_prf, candidate.sk_prf().eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_from_private_key_constant() {
        check_from_private_key(Mode::Constant, 253, 0, 0, 0);
    }

    #[test]
    fn test_from_private_key_public() {
        check_from_private_key(Mode::Public, 0, 0, 253, 254);
    }

    #[test]
    fn test_from_private_key_private() {
        check_from_private_key(Mode::Private, 0, 0, 253, 254);
    }
}
