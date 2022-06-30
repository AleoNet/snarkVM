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

#[cfg(test)]
use snarkvm_circuit_types::environment::assert_scope;

mod to_nonce;
mod to_record_view_key;
mod verify;

use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Boolean, Equal, Field, Group, Scalar, U16};

pub struct Randomizer<A: Aleo> {
    /// The randomizer from the VRF.
    randomizer: Scalar<A>,
    /// The proof for the randomizer: `(gamma, challenge, response)`.
    proof: (Group<A>, Scalar<A>, Scalar<A>),
}

#[cfg(console)]
impl<A: Aleo> Inject for Randomizer<A> {
    type Primitive = console::Randomizer<A::Network>;

    /// Initializes a randomizer from the given mode and native randomizer.
    fn new(mode: Mode, randomizer: Self::Primitive) -> Randomizer<A> {
        Self {
            randomizer: Scalar::new(mode, *randomizer.value()),
            proof: (
                Group::new(mode, randomizer.proof().0),
                Scalar::new(mode, randomizer.proof().1),
                Scalar::new(mode, randomizer.proof().2),
            ),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Randomizer<A> {
    type Primitive = console::Randomizer<A::Network>;

    /// Ejects the mode of the randomizer.
    fn eject_mode(&self) -> Mode {
        (&self.randomizer, &self.proof.0, &self.proof.1, &self.proof.2).eject_mode()
    }

    /// Ejects the randomizer.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from((self.randomizer.eject_value(), (&self.proof).eject_value()))
    }
}

impl<A: Aleo> Randomizer<A> {
    /// Returns the randomizer from the VRF.
    pub const fn value(&self) -> &Scalar<A> {
        &self.randomizer
    }

    /// Returns the proof for the randomizer.
    pub const fn proof(&self) -> &(Group<A>, Scalar<A>, Scalar<A>) {
        &self.proof
    }
}
