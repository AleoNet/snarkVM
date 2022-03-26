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

// pub mod verify;

#[cfg(test)]
use snarkvm_circuits_environment::assert_scope;

use crate::Account;
use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types::{Field, Group, Boolean, Scalar};

pub struct Signature<A: Account> {
    /// The prover response to the challenge.
    prover_response: Scalar<A>,
    /// The verifier challenge to check against.
    verifier_challenge: Scalar<A>,
    /// The x-coordinate of the signature public key `pk_sig` := G^sk_sig.
    pk_sig: Field<A>,
    /// The x-coordinate of the signature public randomizer `pr_sig` := G^r_sig.
    pr_sig: Field<A>,
}

impl<A: Account> Inject for Signature<A> {
    type Primitive = (A::ScalarField, A::ScalarField, A::BaseField, A::BaseField);

    /// Initializes a signature from the given mode and `(prover_response, verifier_challenge, pk_sig, pr_sig)`.
    fn new(mode: Mode, (prover_response, verifier_challenge, pk_sig, pr_sig): Self::Primitive) -> Signature<A> {
        Self {
            prover_response: Scalar::new(mode, prover_response),
            verifier_challenge: Scalar::new(mode, verifier_challenge),
            pk_sig: Field::new(mode, pk_sig),
            pr_sig: Field::new(mode, pr_sig),
        }
    }
}

impl<A: Account> Eject for Signature<A> {
    type Primitive = (A::ScalarField, A::ScalarField, A::BaseField, A::BaseField);

    ///
    /// Ejects the mode of the signature.
    ///
    fn eject_mode(&self) -> Mode {
        (&self.prover_response, &self.verifier_challenge, &self.pk_sig, &self.pr_sig).eject_mode()
    }

    ///
    /// Ejects the signature as `(prover_response, verifier_challenge, pk_sig, pr_sig)`.
    ///
    fn eject_value(&self) -> Self::Primitive {
        (&self.prover_response, &self.verifier_challenge, &self.pk_sig, &self.pr_sig).eject_value()
    }
}
