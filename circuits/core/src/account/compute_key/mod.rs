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

use crate::{account::PrivateKey, Aleo};
use snarkvm_circuits_types::{environment::prelude::*, Group, Scalar};

pub struct ComputeKey<A: Aleo> {
    /// The signature public key `pk_sig` := G^sk_sig.
    pk_sig: Group<A>,
    /// The signature public randomizer `pr_sig` := G^r_sig.
    pr_sig: Group<A>,
    /// The PRF secret key `sk_prf` := RO(G^sk_sig || G^r_sig).
    sk_prf: Scalar<A>,
}

impl<A: Aleo> Inject for ComputeKey<A> {
    type Primitive = (A::Affine, A::Affine, A::ScalarField);

    /// Initializes an account compute key from the given mode and `(pk_sig, pr_sig, sk_prf)`.
    fn new(mode: Mode, (pk_sig, pr_sig, sk_prf): Self::Primitive) -> Self {
        Self { pk_sig: Group::new(mode, pk_sig), pr_sig: Group::new(mode, pr_sig), sk_prf: Scalar::new(mode, sk_prf) }
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

    /// Returns the PRF secret key.
    pub fn sk_prf(&self) -> &Scalar<A> {
        &self.sk_prf
    }
}

impl<A: Aleo> Eject for ComputeKey<A> {
    type Primitive = (A::Affine, A::Affine, A::ScalarField);

    ///
    /// Ejects the mode of the compute key.
    ///
    fn eject_mode(&self) -> Mode {
        (&self.pk_sig, &self.pr_sig, &self.sk_prf).eject_mode()
    }

    ///
    /// Ejects the compute key as `(pk_sig, pr_sig, sk_prf)`.
    ///
    fn eject_value(&self) -> Self::Primitive {
        (&self.pk_sig, &self.pr_sig, &self.sk_prf).eject_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Devnet as Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 1000;

    fn check_new(mode: Mode, num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) {
        let rng = &mut test_rng();

        for _ in 0..ITERATIONS {
            let pk_sig = UniformRand::rand(rng);
            let pr_sig = UniformRand::rand(rng);
            let sk_prf = UniformRand::rand(rng);

            Circuit::scope(format!("New {mode}"), || {
                let candidate = ComputeKey::<Circuit>::new(mode, (pk_sig, pr_sig, sk_prf));
                assert_eq!(mode, candidate.eject_mode());
                assert_eq!((pk_sig, pr_sig, sk_prf), candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_compute_key_new() {
        check_new(Mode::Constant, 259, 0, 0, 0);
        check_new(Mode::Public, 4, 255, 4, 257);
        check_new(Mode::Private, 4, 0, 259, 257);
    }
}
