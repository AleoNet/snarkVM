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
use snarkvm_circuits_types::{Group, Scalar};

pub struct ComputeKey<E: Environment> {
    /// pk_sig := G^sk_sig.
    pk_sig: Group<E>,
    /// pr_sig := G^r_sig.
    pr_sig: Group<E>,
    /// sk_prf := RO(G^sk_sig || G^r_sig).
    sk_prf: Scalar<E>,
}

impl<E: Environment> Inject for ComputeKey<E> {
    type Primitive = (E::Affine, E::Affine, E::ScalarField);

    /// Initializes an account compute key from the given mode and `(pk_sig, pr_sig, sk_prf)`.
    fn new(mode: Mode, (pk_sig, pr_sig, sk_prf): Self::Primitive) -> ComputeKey<E> {
        Self { pk_sig: Group::new(mode, pk_sig), pr_sig: Group::new(mode, pr_sig), sk_prf: Scalar::new(mode, sk_prf) }
    }
}

impl<E: Environment> Eject for ComputeKey<E> {
    type Primitive = (E::Affine, E::Affine, E::ScalarField);

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
