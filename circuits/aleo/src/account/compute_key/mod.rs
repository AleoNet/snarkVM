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

pub mod from_private_key;

#[cfg(test)]
use snarkvm_circuits_types::environment::assert_scope;

use crate::PrivateKey;
use snarkvm_circuits_network::Aleo;
use snarkvm_circuits_types::{environment::prelude::*, Group, Scalar};

pub struct ComputeKey<A: Aleo> {
    /// The signature public key `pk_sig` := G^sk_sig.
    pk_sig: Group<A>,
    /// The signature public randomizer `pr_sig` := G^r_sig.
    pr_sig: Group<A>,
    /// The VRF public key `pk_vrf` := G^sk_vrf.
    pk_vrf: Group<A>,
    /// The PRF secret key `sk_prf` := RO(G^sk_sig || G^r_sig).
    sk_prf: Scalar<A>,
}

#[cfg(console)]
impl<A: Aleo> Inject for ComputeKey<A> {
    type Primitive = (A::Affine, A::Affine, A::Affine);

    /// Initializes an account compute key from the given mode and `(pk_sig, pr_sig, pk_vrf)`.
    fn new(mode: Mode, (pk_sig, pr_sig, pk_vrf): Self::Primitive) -> Self {
        // Inject `pk_sig`.
        let pk_sig = Group::new(mode, pk_sig);
        // Inject `pr_sig`.
        let pr_sig = Group::new(mode, pr_sig);
        // Inject `pk_vrf`.
        let pk_vrf = Group::new(mode, pk_vrf);
        // Compute `sk_prf` := HashToScalar(G^sk_sig || G^r_sig || G^sk_vrf).
        let sk_prf =
            A::hash_to_scalar_psd4(&[pk_sig.to_x_coordinate(), pr_sig.to_x_coordinate(), pk_vrf.to_x_coordinate()]);
        // Output the compute key.
        Self { pk_sig, pr_sig, pk_vrf, sk_prf }
    }
}

impl<A: Aleo> ComputeKey<A> {
    /// Returns the signature public key.
    pub fn pk_sig(&self) -> &Group<A> {
        &self.pk_sig
    }

    /// Returns the signature public randomizer.
    pub fn pr_sig(&self) -> &Group<A> {
        &self.pr_sig
    }

    /// Returns the VRF public key.
    pub fn pk_vrf(&self) -> &Group<A> {
        &self.pk_vrf
    }

    /// Returns the PRF secret key.
    pub fn sk_prf(&self) -> &Scalar<A> {
        &self.sk_prf
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for ComputeKey<A> {
    type Primitive = (A::Affine, A::Affine, A::Affine, A::ScalarField);

    /// Ejects the mode of the compute key.
    fn eject_mode(&self) -> Mode {
        (&self.pk_sig, &self.pr_sig, &self.pk_vrf, &self.sk_prf).eject_mode()
    }

    /// Ejects the compute key as `(pk_sig, pr_sig, pk_vrf, sk_prf)`.
    fn eject_value(&self) -> Self::Primitive {
        (&self.pk_sig, &self.pr_sig, &self.pk_vrf, &self.sk_prf).eject_value()
    }
}

#[cfg(all(test, console))]
pub(crate) mod tests {
    use super::*;
    use crate::{account::helpers::generate_account, Circuit};

    use anyhow::Result;

    const ITERATIONS: u64 = 1000;

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

            // Retrieve the native compute key components.
            let pk_sig = compute_key.pk_sig();
            let pr_sig = compute_key.pr_sig();
            let pk_vrf = compute_key.pk_vrf();
            let sk_prf = compute_key.sk_prf();

            Circuit::scope(format!("New {mode}"), || {
                let candidate = ComputeKey::<Circuit>::new(mode, (pk_sig, pr_sig, pk_vrf));
                match mode.is_constant() {
                    true => assert_eq!(Mode::Constant, candidate.eject_mode()),
                    false => assert_eq!(Mode::Private, candidate.eject_mode()),
                };
                assert_eq!((pk_sig, pr_sig, pk_vrf, sk_prf), candidate.eject_value());
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
        check_new(Mode::Constant, 265, 0, 0, 0)
    }

    #[test]
    fn test_compute_key_new_public() -> Result<()> {
        check_new(Mode::Public, 6, 6, 604, 608)
    }

    #[test]
    fn test_compute_key_new_private() -> Result<()> {
        check_new(Mode::Private, 6, 0, 610, 608)
    }
}
