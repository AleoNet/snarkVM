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

mod to_root;

use crate::traits::Hash;
use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types::Boolean;

// TODO (raychu86): Remove use of `INPUT_SIZE_FE` as it is merely a requirement for
//  the `PoseidonCRH` implementation. Ideally merkle trees are updated to deal directly
//  with bits and field elements instead of bytes to prevent padding requirements.
pub struct MerklePath<E: Environment, H: Hash, const INPUT_SIZE_FE: usize> {
    /// `traversal[i]` is 0 (false) iff ith node from bottom to top is left.
    traversal: Vec<Boolean<E>>,
    /// `path[i]` is the entry of sibling of ith node from bottom to top.
    path: Vec<H::Input>,
}

impl<E: Environment, H: Hash, const INPUT_SIZE_FE: usize> Inject for MerklePath<E, H, INPUT_SIZE_FE> {
    type Primitive = (Vec<bool>, Vec<<H::Input as Inject>::Primitive>);

    /// Initializes a merkle path from the given mode and `path`.
    fn new(mode: Mode, (traversal, path): Self::Primitive) -> Self {
        let mut circuit_traversal = vec![];
        for position in traversal.iter() {
            circuit_traversal.push(Boolean::new(mode, *position));
        }

        let mut circuit_path = vec![];
        for node in path.into_iter() {
            circuit_path.push(H::Input::new(mode, node));
        }

        Self { traversal: circuit_traversal, path: circuit_path }
    }
}

impl<E: Environment, H: Hash, const INPUT_SIZE_FE: usize> Eject for MerklePath<E, H, INPUT_SIZE_FE> {
    type Primitive = (Vec<bool>, Vec<<H::Input as Eject>::Primitive>);

    ///
    /// Ejects the mode of the merkle path.
    ///
    fn eject_mode(&self) -> Mode {
        (&self.traversal, &self.path).eject_mode()
    }

    ///
    /// Ejects the merkle path as `(traversal, path)`.
    ///
    fn eject_value(&self) -> Self::Primitive {
        (&self.traversal, &self.path).eject_value()
    }
}
