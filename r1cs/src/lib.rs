// Copyright (C) 2019-2023 Aleo Systems Inc.
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

#[macro_use]
extern crate thiserror;

mod assignment;
pub use assignment::*;

mod constraint_counter;
pub use constraint_counter::*;

mod constraint_system;
pub use constraint_system::{ConstraintSynthesizer, ConstraintSystem};

mod constraint_variable;
pub use constraint_variable::*;

pub mod errors;
pub use errors::*;

mod linear_combination;
pub use linear_combination::*;

mod namespace;
pub use namespace::*;

mod optional_vec;
pub use optional_vec::*;

mod test_constraint_system;
pub use test_constraint_system::{Fr, TestConstraintSystem};

mod test_constraint_checker;
pub use test_constraint_checker::TestConstraintChecker;

use snarkvm_utilities::serialize::*;

use std::cmp::Ordering;

/// Represents a variable in a constraint system.
#[derive(PartialOrd, Ord, PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub struct Variable(Index);

impl Variable {
    /// This constructs a variable with an arbitrary index.
    /// Circuit implementations are not recommended to use this.
    pub fn new_unchecked(idx: Index) -> Variable {
        Variable(idx)
    }

    /// This returns the index underlying the variable.
    /// Circuit implementations are not recommended to use this.
    pub fn get_unchecked(&self) -> Index {
        self.0
    }
}

/// Represents the index of either a public variable (input) or a private variable (auxiliary).
#[derive(Copy, Clone, PartialEq, Debug, Eq, Hash)]
pub enum Index {
    /// Index of an public variable.
    Public(usize),
    /// Index of an private variable.
    Private(usize),
}

impl PartialOrd for Index {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Index {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Index::Public(ref idx1), Index::Public(ref idx2))
            | (Index::Private(ref idx1), Index::Private(ref idx2)) => idx1.cmp(idx2),
            (Index::Public(_), Index::Private(_)) => Ordering::Less,
            (Index::Private(_), Index::Public(_)) => Ordering::Greater,
        }
    }
}

impl CanonicalSerialize for Index {
    #[inline]
    fn serialize_with_mode<W: Write>(&self, mut writer: W, _: Compress) -> Result<(), SerializationError> {
        let (is_public, inner) = match *self {
            Index::Public(inner) => (true, inner),
            Index::Private(inner) => (false, inner),
        };
        // we use uncompressed here because the serialization of bool and usize
        // don't change whether we use uncompressed or not.
        is_public.serialize_uncompressed(&mut writer)?;
        inner.serialize_uncompressed(&mut writer)?;
        Ok(())
    }

    #[inline]
    fn serialized_size(&self, _: Compress) -> usize {
        // we use uncompressed here because the serialization of bool and usize
        // don't change whether we use uncompressed or not.
        0usize.uncompressed_size() + true.uncompressed_size()
    }
}

impl Valid for Index {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}
impl CanonicalDeserialize for Index {
    #[inline]
    fn deserialize_with_mode<R: Read>(mut reader: R, _: Compress, _: Validate) -> Result<Self, SerializationError> {
        // we use uncompressed here because the serialization of bool and usize
        // don't change whether we use uncompressed or not.
        let is_input = bool::deserialize_uncompressed(&mut reader)?;
        let inner = usize::deserialize_uncompressed(&mut reader)?;
        Ok(if is_input { Index::Public(inner) } else { Index::Private(inner) })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn serialize_index() {
        serialize_index_test(true);
        serialize_index_test(false);
    }

    fn serialize_index_test(input: bool) {
        let idx = if input { Index::Public(32) } else { Index::Private(32) };

        let mut v = vec![];
        idx.serialize_compressed(&mut v).unwrap();
        let idx2 = Index::deserialize_compressed(&v[..]).unwrap();
        assert_eq!(idx, idx2);
    }
}
