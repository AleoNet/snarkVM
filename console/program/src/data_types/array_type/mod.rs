// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod bytes;
mod parse;
mod serialize;

use crate::{Identifier, LiteralType, PlaintextType, U32};
use snarkvm_console_network::prelude::*;

use core::fmt::{Debug, Display};

/// An `ArrayType` defines the type and size of an array.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ArrayType<N: Network> {
    /// An array of literals.
    Literal(LiteralType, U32<N>),
    /// An array of structs.
    Struct(Identifier<N>, U32<N>),
}

impl<N: Network> ArrayType<N> {
    /// Initializes a new array type composed of literals.
    pub fn new_literal(literal_type: LiteralType, length: U32<N>) -> Result<Self> {
        ensure!(*length as usize >= N::MIN_ARRAY_ENTRIES, "An array must have {} element", N::MIN_ARRAY_ENTRIES);
        ensure!(*length as usize <= N::MAX_ARRAY_ENTRIES, "An array can contain {} elements", N::MAX_ARRAY_ENTRIES);
        Ok(Self::Literal(literal_type, length))
    }

    /// Initializes a new array type composed of structs.
    pub fn new_struct(struct_: Identifier<N>, length: U32<N>) -> Result<Self> {
        ensure!(*length as usize >= N::MIN_ARRAY_ENTRIES, "An array must have {} element", N::MIN_ARRAY_ENTRIES);
        ensure!(*length as usize <= N::MAX_ARRAY_ENTRIES, "An array can contain {} elements", N::MAX_ARRAY_ENTRIES);
        Ok(Self::Struct(struct_, length))
    }
}

impl<N: Network> ArrayType<N> {
    /// Returns the element type.
    pub const fn element_type(&self) -> PlaintextType<N> {
        match &self {
            ArrayType::Literal(literal_type, ..) => PlaintextType::Literal(*literal_type),
            ArrayType::Struct(identifier, ..) => PlaintextType::Struct(*identifier),
        }
    }

    /// Returns `true` if the array is empty.
    pub fn is_empty(&self) -> bool {
        match &self {
            ArrayType::Literal(_, length) => **length == 0,
            ArrayType::Struct(_, length) => **length == 0,
        }
    }

    /// Returns the length of the array.
    pub const fn length(&self) -> &U32<N> {
        match &self {
            ArrayType::Literal(_, length) => length,
            ArrayType::Struct(_, length) => length,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    use core::str::FromStr;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_array_type() -> Result<()> {
        // Test literal array types.
        let array = ArrayType::<CurrentNetwork>::from_str("[field; 4]")?;
        assert_eq!(array, ArrayType::<CurrentNetwork>::Literal(LiteralType::Field, U32::new(4)));
        assert_eq!(
            array.to_bytes_le()?,
            ArrayType::<CurrentNetwork>::from_bytes_le(&array.to_bytes_le()?)?.to_bytes_le()?
        );
        assert_eq!(array.element_type(), PlaintextType::Literal(LiteralType::Field));
        assert_eq!(array.length(), &U32::new(4));
        assert!(!array.is_empty());

        // Test struct array types.
        let array = ArrayType::<CurrentNetwork>::from_str("[foo; 1]")?;
        assert_eq!(array, ArrayType::<CurrentNetwork>::Struct(Identifier::from_str("foo")?, U32::new(1)));
        assert_eq!(
            array.to_bytes_le()?,
            ArrayType::<CurrentNetwork>::from_bytes_le(&array.to_bytes_le()?)?.to_bytes_le()?
        );
        assert_eq!(array.element_type(), PlaintextType::Struct(Identifier::from_str("foo")?));
        assert_eq!(array.length(), &U32::new(1));
        assert!(!array.is_empty());

        // Test array type with maximum length.
        let array = ArrayType::<CurrentNetwork>::from_str("[scalar; 32]")?;
        assert_eq!(array, ArrayType::<CurrentNetwork>::Literal(LiteralType::Scalar, U32::new(32)));
        assert_eq!(
            array.to_bytes_le()?,
            ArrayType::<CurrentNetwork>::from_bytes_le(&array.to_bytes_le()?)?.to_bytes_le()?
        );
        assert_eq!(array.element_type(), PlaintextType::Literal(LiteralType::Scalar));
        assert_eq!(array.length(), &U32::new(32));
        assert!(!array.is_empty());

        Ok(())
    }

    #[test]
    fn test_array_type_fails() {
        let type_ = ArrayType::<CurrentNetwork>::from_str("[field; 0]");
        assert!(type_.is_err());

        let type_ = ArrayType::<CurrentNetwork>::from_str("[field; 4294967296]");
        assert!(type_.is_err());

        let type_ = ArrayType::<CurrentNetwork>::from_str("[foo; -1]");
        assert!(type_.is_err());
    }
}
