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

mod from_private_key;
mod to_address;

#[cfg(test)]
use snarkvm_circuit_types::environment::assert_scope;

use crate::PrivateKey;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Group, Scalar};

pub struct ComputeKey<A: Aleo> {
    /// The signature public key `pk_sig` := G^sk_sig.
    pk_sig: Group<A>,
    /// The signature public randomizer `pr_sig` := G^r_sig.
    pr_sig: Group<A>,
    /// The PRF secret key `sk_prf` := RO(G^sk_sig || G^r_sig).
    sk_prf: Scalar<A>,
}

#[cfg(console)]
impl<A: Aleo> Inject for ComputeKey<A> {
    type Primitive = console::ComputeKey<A::Network>;

    /// Initializes an account compute key from the given mode and native compute key.
    fn new(mode: Mode, compute_key: Self::Primitive) -> Self {
        // Inject `pk_sig`.
        let pk_sig = Group::new(mode, compute_key.pk_sig());
        // Inject `pr_sig`.
        let pr_sig = Group::new(mode, compute_key.pr_sig());
        // Compute `sk_prf` := HashToScalar(G^sk_sig || G^r_sig).
        let sk_prf = A::hash_to_scalar_psd4(&[pk_sig.to_x_coordinate(), pr_sig.to_x_coordinate()]);
        // Output the compute key.
        Self { pk_sig, pr_sig, sk_prf }
    }
}

impl<A: Aleo> ComputeKey<A> {
    /// Returns the signature public key.
    pub const fn pk_sig(&self) -> &Group<A> {
        &self.pk_sig
    }

    /// Returns the signature public randomizer.
    pub const fn pr_sig(&self) -> &Group<A> {
        &self.pr_sig
    }

    /// Returns the PRF secret key.
    pub const fn sk_prf(&self) -> &Scalar<A> {
        &self.sk_prf
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for ComputeKey<A> {
    type Primitive = console::ComputeKey<A::Network>;

    /// Ejects the mode of the compute key.
    fn eject_mode(&self) -> Mode {
        (&self.pk_sig, &self.pr_sig, &self.sk_prf).eject_mode()
    }

    /// Ejects the compute key.
    fn eject_value(&self) -> Self::Primitive {
        match Self::Primitive::try_from((&self.pk_sig, &self.pr_sig).eject_value()) {
            Ok(compute_key) => compute_key,
            Err(error) => A::halt(format!("Failed to eject the compute key: {error}")),
        }
    }
}

#[cfg(all(test, console))]
pub(crate) mod tests {
    use super::*;
    use crate::{helpers::generate_account, Circuit};

    use anyhow::Result;

    const ITERATIONS: u64 = 250;

    fn check_new(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        for i in 0..ITERATIONS {
            // Generate a private key, compute key, view key, and address.
            let (_private_key, compute_key, _view_key, _address) = generate_account()?;

            Circuit::scope(format!("New {mode}"), || {
                let candidate = ComputeKey::<Circuit>::new(mode, compute_key);
                match mode.is_constant() {
                    true => assert_eq!(Mode::Constant, candidate.eject_mode()),
                    false => assert_eq!(Mode::Private, candidate.eject_mode()),
                };
                assert_eq!(compute_key, candidate.eject_value());
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
    fn test_compute_key_new_constant() -> Result<()> {
        check_new(Mode::Constant, 262, 0, 0, 0)
    }

    #[test]
    fn test_compute_key_new_public() -> Result<()> {
        check_new(Mode::Public, 5, 4, 597, 600)
    }

    #[test]
    fn test_compute_key_new_private() -> Result<()> {
        check_new(Mode::Private, 5, 0, 601, 600)
    }
}
