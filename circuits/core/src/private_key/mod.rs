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

use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types::Scalar;

pub struct PrivateKey<E: Environment> {
    /// The signature secret key.
    sk_sig: Scalar<E>,
    /// The signature randomizer.
    r_sig: Scalar<E>,
}

impl<E: Environment> Inject for PrivateKey<E> {
    type Primitive = (E::ScalarField, E::ScalarField);

    /// Initializes an account private key from the given mode and `(sk_sig, r_sig)`.
    fn new(mode: Mode, (sk_sig, r_sig): Self::Primitive) -> PrivateKey<E> {
        Self { sk_sig: Scalar::new(mode, sk_sig), r_sig: Scalar::new(mode, r_sig) }
    }
}

impl<E: Environment> Eject for PrivateKey<E> {
    type Primitive = (E::ScalarField, E::ScalarField);

    ///
    /// Ejects the mode of the account private key.
    ///
    fn eject_mode(&self) -> Mode {
        (&self.sk_sig, &self.r_sig).eject_mode()
    }

    ///
    /// Ejects the account private key as `(sk_sig, r_sig)`.
    ///
    fn eject_value(&self) -> Self::Primitive {
        (&self.sk_sig, &self.r_sig).eject_value()
    }
}
