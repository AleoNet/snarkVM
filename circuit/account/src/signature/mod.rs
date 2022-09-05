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

mod verify;

#[cfg(test)]
use snarkvm_circuit_types::environment::assert_scope;

use crate::ComputeKey;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Boolean, Field, Scalar};

pub struct Signature<A: Aleo> {
    /// The verifier challenge to check against.
    challenge: Scalar<A>,
    /// The prover response to the challenge.
    response: Scalar<A>,
    /// The compute key of the prover.
    compute_key: ComputeKey<A>,
}

#[cfg(console)]
impl<A: Aleo> Inject for Signature<A> {
    type Primitive = console::Signature<A::Network>;

    /// Initializes a signature from the given mode and native signature.
    fn new(mode: Mode, signature: Self::Primitive) -> Signature<A> {
        Self {
            challenge: Scalar::new(mode, signature.challenge()),
            response: Scalar::new(mode, signature.response()),
            compute_key: ComputeKey::new(mode, signature.compute_key()),
        }
    }
}

impl<A: Aleo> Signature<A> {
    /// Returns the challenge.
    pub const fn challenge(&self) -> &Scalar<A> {
        &self.challenge
    }

    /// Returns the response.
    pub const fn response(&self) -> &Scalar<A> {
        &self.response
    }

    /// Returns the account compute key.
    pub const fn compute_key(&self) -> &ComputeKey<A> {
        &self.compute_key
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Signature<A> {
    type Primitive = console::Signature<A::Network>;

    /// Ejects the mode of the signature.
    fn eject_mode(&self) -> Mode {
        (&self.challenge, &self.response, &self.compute_key).eject_mode()
    }

    /// Ejects the signature.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from((&self.challenge, &self.response, &self.compute_key).eject_value())
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::{helpers::generate_account, Circuit};
    use snarkvm_utilities::{test_crypto_rng, Uniform};

    use anyhow::Result;

    const ITERATIONS: u64 = 250;

    fn check_new(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        let rng = &mut test_crypto_rng();

        // Generate a private key, compute key, view key, and address.
        let (private_key, _compute_key, _view_key, _address) = generate_account()?;

        for i in 0..ITERATIONS {
            // Generate a signature.
            let message: Vec<_> = (0..i).map(|_| Uniform::rand(rng)).collect();
            let signature = console::Signature::sign(&private_key, &message, rng)?;

            Circuit::scope(format!("New {mode}"), || {
                let candidate = Signature::<Circuit>::new(mode, signature);
                assert_eq!(signature, candidate.eject_value());
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
        check_new(Mode::Constant, 264, 0, 0, 0)
    }

    #[test]
    fn test_signature_new_public() -> Result<()> {
        check_new(Mode::Public, 5, 6, 597, 600)
    }

    #[test]
    fn test_signature_new_private() -> Result<()> {
        check_new(Mode::Private, 5, 0, 603, 600)
    }
}
