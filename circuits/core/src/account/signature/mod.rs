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

use crate::Aleo;
use snarkvm_circuits_types::{environment::prelude::*, Address, Boolean, Field, Group, Literal, Scalar};

pub struct Signature<A: Aleo> {
    /// The prover response to the challenge.
    prover_response: Scalar<A>,
    /// The verifier challenge to check against.
    verifier_challenge: Scalar<A>,
    /// The x-coordinate of the signature public key `pk_sig` := G^sk_sig.
    pk_sig: Group<A>,
    /// The x-coordinate of the signature public randomizer `pr_sig` := G^r_sig.
    pr_sig: Group<A>,
}

impl<A: Aleo> Inject for Signature<A> {
    type Primitive = (A::ScalarField, A::ScalarField, A::BaseField, A::BaseField);

    /// Initializes a signature from the given mode and `(prover_response, verifier_challenge, pk_sig, pr_sig)`.
    fn new(mode: Mode, (prover_response, verifier_challenge, pk_sig, pr_sig): Self::Primitive) -> Signature<A> {
        Self {
            prover_response: Scalar::new(mode, prover_response),
            verifier_challenge: Scalar::new(mode, verifier_challenge),
            pk_sig: Group::from_x_coordinate(Field::new(mode, pk_sig)),
            pr_sig: Group::from_x_coordinate(Field::new(mode, pr_sig)),
        }
    }
}

impl<A: Aleo> Eject for Signature<A> {
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
        (
            &self.prover_response,
            &self.verifier_challenge,
            &self.pk_sig.to_x_coordinate(),
            &self.pr_sig.to_x_coordinate(),
        )
            .eject_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Devnet as Circuit;
    use snarkvm_curves::AffineCurve;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 1000;

    fn check_new(mode: Mode, num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) {
        let rng = &mut test_rng();

        for _ in 0..ITERATIONS {
            let prover_response = UniformRand::rand(rng);
            let verifier_challenge = UniformRand::rand(rng);
            let pk_sig = <Circuit as Environment>::Affine::rand(rng).to_x_coordinate();
            let pr_sig = <Circuit as Environment>::Affine::rand(rng).to_x_coordinate();

            Circuit::scope(format!("New {mode}"), || {
                let candidate = Signature::<Circuit>::new(mode, (prover_response, verifier_challenge, pk_sig, pr_sig));
                assert_eq!((prover_response, verifier_challenge, pk_sig, pr_sig), candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_signature_new() {
        check_new(Mode::Constant, 510, 0, 0, 0);
        check_new(Mode::Public, 4, 504, 6, 508);
        check_new(Mode::Private, 4, 0, 510, 508);
    }
}
