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
use snarkvm_circuits_environment::assert_scope;

use crate::{Account, PrivateKey};
use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types::{Group, Scalar};

pub struct ComputeKey<A: Account> {
    /// The signature public key `pk_sig` := G^sk_sig.
    pk_sig: Group<A>,
    /// The signature public randomizer `pr_sig` := G^r_sig.
    pr_sig: Group<A>,
    /// The PRF secret key `sk_prf` := RO(G^sk_sig || G^r_sig).
    sk_prf: Scalar<A>,
}

impl<A: Account> Inject for ComputeKey<A> {
    type Primitive = (A::Affine, A::Affine, A::ScalarField);

    /// Initializes an account compute key from the given mode and `(pk_sig, pr_sig, sk_prf)`.
    fn new(mode: Mode, (pk_sig, pr_sig, sk_prf): Self::Primitive) -> Self {
        Self { pk_sig: Group::new(mode, pk_sig), pr_sig: Group::new(mode, pr_sig), sk_prf: Scalar::new(mode, sk_prf) }
    }
}

impl<A: Account> ComputeKey<A> {
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

impl<A: Account> Eject for ComputeKey<A> {
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
