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

use circuit::{
    network::Aleo,
    program::{Identifier, ProgramID},
    types::{environment::prelude::*, Boolean, Field, U16, U8},
};

#[derive(Clone)]
pub struct TransactionLeaf<A: Aleo> {
    /// The variant of the Merkle leaf.
    variant: U8<A>,
    /// The index of the Merkle leaf.
    index: U16<A>,
    /// The program ID.
    program_id: ProgramID<A>,
    /// The function name.
    function_name: Identifier<A>,
    /// The ID.
    id: Field<A>,
}

impl<A: Aleo> TransactionLeaf<A> {
    /// Returns the ID in the Merkle leaf.
    pub const fn id(&self) -> &Field<A> {
        &self.id
    }
}

impl<A: Aleo> Inject for TransactionLeaf<A> {
    type Primitive = crate::ledger::state_path::TransactionLeaf<A::Network>;

    /// Initializes a new transaction leaf circuit from a primitive.
    fn new(mode: Mode, transaction_leaf: Self::Primitive) -> Self {
        Self {
            variant: U8::new(mode, console::types::U8::new(transaction_leaf.variant())),
            index: U16::new(mode, console::types::U16::new(transaction_leaf.index())),
            program_id: ProgramID::new(mode, transaction_leaf.program_id()),
            function_name: Identifier::new(mode, transaction_leaf.function_name()),
            id: Field::new(mode, transaction_leaf.id()),
        }
    }
}

impl<A: Aleo> Eject for TransactionLeaf<A> {
    type Primitive = crate::ledger::state_path::TransactionLeaf<A::Network>;

    /// Ejects the mode of the transaction leaf.
    fn eject_mode(&self) -> Mode {
        (&self.variant, &self.index, &self.program_id, &self.function_name, &self.id).eject_mode()
    }

    /// Ejects the transaction leaf.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::new(
            *self.variant.eject_value(),
            *self.index.eject_value(),
            self.program_id.eject_value(),
            self.function_name.eject_value(),
            self.id.eject_value(),
        )
    }
}

impl<A: Aleo> ToBits for TransactionLeaf<A> {
    type Boolean = Boolean<A>;

    /// Outputs the little-endian bit representation of `self` *without* trailing zeros.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        let mut bits_le = self.variant.to_bits_le();
        bits_le.extend(self.index.to_bits_le());
        bits_le.extend(self.program_id.to_bits_le());
        bits_le.extend(self.function_name.to_bits_le());
        bits_le.extend(self.id.to_bits_le());
        bits_le
    }

    /// Outputs the big-endian bit representation of `self` *without* leading zeros.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits_be = self.variant.to_bits_be();
        bits_be.extend(self.index.to_bits_be());
        bits_be.extend(self.program_id.to_bits_be());
        bits_be.extend(self.function_name.to_bits_be());
        bits_be.extend(self.id.to_bits_be());
        bits_be
    }
}
