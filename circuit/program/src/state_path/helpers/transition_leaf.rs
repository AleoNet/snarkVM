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

use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field, U16, U8};

#[derive(Clone)]
pub struct TransitionLeaf<A: Aleo> {
    /// The version of the Merkle leaf.
    version: U8<A>,
    /// The index of the Merkle leaf.
    index: U8<A>,
    /// The variant of the Merkle leaf.
    variant: U16<A>,
    /// The ID.
    id: Field<A>,
}

impl<A: Aleo> TransitionLeaf<A> {
    /// Returns the version of the Merkle leaf.
    pub const fn version(&self) -> &U8<A> {
        &self.version
    }

    /// Returns the index of the Merkle leaf.
    pub const fn index(&self) -> &U8<A> {
        &self.index
    }

    /// Returns the variant of the Merkle leaf.
    pub const fn variant(&self) -> &U16<A> {
        &self.variant
    }

    /// Returns the ID in the Merkle leaf.
    pub const fn id(&self) -> &Field<A> {
        &self.id
    }
}

impl<A: Aleo> Inject for TransitionLeaf<A> {
    type Primitive = console::TransitionLeaf<A::Network>;

    /// Initializes a new transition leaf circuit from a primitive.
    fn new(mode: Mode, transition_leaf: Self::Primitive) -> Self {
        Self {
            version: U8::new(mode, console::U8::new(transition_leaf.version())),
            index: U8::new(mode, console::U8::new(transition_leaf.index())),
            variant: U16::new(mode, console::U16::new(transition_leaf.variant())),
            id: Field::new(mode, transition_leaf.id()),
        }
    }
}

impl<A: Aleo> Eject for TransitionLeaf<A> {
    type Primitive = console::TransitionLeaf<A::Network>;

    /// Ejects the mode of the transition leaf.
    fn eject_mode(&self) -> Mode {
        (&self.version, &self.index, &self.variant, &self.id).eject_mode()
    }

    /// Ejects the transition leaf.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from(
            *self.version.eject_value(),
            *self.index.eject_value(),
            *self.variant.eject_value(),
            self.id.eject_value(),
        )
    }
}

impl<A: Aleo> ToBits for TransitionLeaf<A> {
    type Boolean = Boolean<A>;

    /// Outputs the little-endian bit representation of `self` *without* trailing zeros.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        let mut bits_le = self.version.to_bits_le();
        bits_le.extend(self.index.to_bits_le());
        bits_le.extend(self.variant.to_bits_le());
        bits_le.extend(self.id.to_bits_le());
        bits_le
    }

    /// Outputs the big-endian bit representation of `self` *without* leading zeros.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits_be = self.version.to_bits_be();
        bits_be.extend(self.index.to_bits_be());
        bits_be.extend(self.variant.to_bits_be());
        bits_be.extend(self.id.to_bits_be());
        bits_be
    }
}
