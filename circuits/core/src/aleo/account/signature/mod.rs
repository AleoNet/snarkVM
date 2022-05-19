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

pub mod verify;

#[cfg(test)]
use snarkvm_circuits_types::environment::assert_scope;

use crate::aleo::{Aleo, ComputeKey};
use snarkvm_circuits_types::{environment::prelude::*, Address, Boolean, Field, Literal, Scalar, ToBits};

pub struct Signature<A: Aleo> {
    /// The verifier challenge to check against.
    challenge: Scalar<A>,
    /// The prover response to the challenge.
    response: Scalar<A>,
    /// The compute key of the prover.
    compute_key: ComputeKey<A>,
}

impl<A: Aleo> Inject for Signature<A> {
    type Primitive = (A::ScalarField, A::ScalarField, (A::Affine, A::Affine, A::Affine));

    /// Initializes a signature from the given mode and `(challenge, response, (pk_sig, pr_sig, pk_vrf))`.
    fn new(mode: Mode, (challenge, response, (pk_sig, pr_sig, pk_vrf)): Self::Primitive) -> Signature<A> {
        Self {
            challenge: Scalar::new(mode, challenge),
            response: Scalar::new(mode, response),
            compute_key: ComputeKey::new(mode, (pk_sig, pr_sig, pk_vrf)),
        }
    }
}

impl<A: Aleo> Eject for Signature<A> {
    type Primitive = (A::ScalarField, A::ScalarField, (A::Affine, A::Affine, A::Affine, A::ScalarField));

    ///
    /// Ejects the mode of the signature.
    ///
    fn eject_mode(&self) -> Mode {
        (&self.challenge, &self.response, &self.compute_key).eject_mode()
    }

    ///
    /// Ejects the signature as `(challenge, response, (pk_sig, pr_sig, pk_vrf, sk_prf))`.
    ///
    fn eject_value(&self) -> Self::Primitive {
        (&self.challenge, &self.response, &self.compute_key).eject_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aleo::{account::helpers::generate_account, Devnet as Circuit};
    use snarkvm_console_aleo::Signature as NativeSignature;
    use snarkvm_utilities::{test_crypto_rng, ToBits as T, UniformRand};

    use anyhow::Result;

    const ITERATIONS: u64 = 1000;

    fn check_new(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        // Generate a private key, compute key, view key, and address.
        let (private_key, compute_key, _view_key, _address) = generate_account()?;

        // Retrieve the native compute key components.
        let pk_sig = *compute_key.pk_sig();
        let pr_sig = *compute_key.pr_sig();
        let pk_vrf = *compute_key.pk_vrf();
        let sk_prf = *compute_key.sk_prf();

        for i in 0..ITERATIONS {
            // Generate a signature.
            let message = "Hi, I am an Aleo signature!";
            let randomizer = UniformRand::rand(&mut test_crypto_rng());
            let signature = NativeSignature::sign(&private_key, &message.as_bytes().to_bits_le(), randomizer)?;

            // Retrieve the challenge and response.
            let challenge = *signature.challenge();
            let response = *signature.response();

            Circuit::scope(format!("New {mode}"), || {
                let candidate = Signature::<Circuit>::new(mode, (challenge, response, (pk_sig, pr_sig, pk_vrf)));
                assert_eq!((challenge, response, (pk_sig, pr_sig, pk_vrf, sk_prf)), candidate.eject_value());
                // TODO (howardwu): Resolve skipping the cost count checks for the burn-in round.
                if i > 0 {
                    assert_scope!(num_constants, num_public, num_private, num_constraints);
                }
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_signature_new_constant() -> Result<()> {
        check_new(Mode::Constant, 767, 0, 0, 0)
    }

    #[test]
    fn test_signature_new_public() -> Result<()> {
        check_new(Mode::Public, 6, 508, 604, 1110)
    }

    #[test]
    fn test_signature_new_private() -> Result<()> {
        check_new(Mode::Private, 6, 0, 1112, 1110)
    }
}
