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

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ArrayType<N: Network> {
    /// An array of literals.
    Literal(LiteralType, U32<N>),
    /// An array of structs.
    Struct(Identifier<N>, U32<N>),
}

impl<N: Network> ArrayType<N> {
    /// Constructs a new type defining an array of literals.
    pub fn new_literal_array(literal_type: LiteralType, length: U32<N>) -> Result<Self> {
        ensure!(*length != 0, "The array must have at least one element");
        // TODO (d0cd): Is there an explicit maximum length of an array?
        Ok(Self::Literal(literal_type, length))
    }

    /// Constructs a new type defining an array of structs.
    pub fn new_struct_array(struct_: Identifier<N>, length: U32<N>) -> Result<Self> {
        ensure!(*length != 0, "The array must have at least one element");
        // TODO (d0cd): Is there an explicit maximum length of an array?
        Ok(Self::Struct(struct_, length))
    }

    /// Returns the element type.
    pub fn element_type(&self) -> PlaintextType<N> {
        match &self {
            ArrayType::Literal(literal_type, ..) => PlaintextType::Literal(*literal_type),
            ArrayType::Struct(identifier, ..) => PlaintextType::Struct(*identifier),
        }
    }

    /// Returns the length of the array.
    pub fn length(&self) -> &U32<N> {
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
        let type_ = ArrayType::<CurrentNetwork>::from_str("[field; 4]")?;
        assert_eq!(type_, ArrayType::<CurrentNetwork>::Literal(LiteralType::Field, U32::new(4)));
        assert_eq!(
            type_.to_bytes_le()?,
            ArrayType::<CurrentNetwork>::from_bytes_le(&type_.to_bytes_le()?)?.to_bytes_le()?
        );
        assert_eq!(type_.element_type(), PlaintextType::Literal(LiteralType::Field));
        assert_eq!(type_.length(), &U32::new(4));

        let type_ = ArrayType::<CurrentNetwork>::from_str("[foo; 1]")?;
        assert_eq!(type_, ArrayType::<CurrentNetwork>::Struct(Identifier::from_str("foo")?, U32::new(1)));
        assert_eq!(
            type_.to_bytes_le()?,
            ArrayType::<CurrentNetwork>::from_bytes_le(&type_.to_bytes_le()?)?.to_bytes_le()?
        );
        assert_eq!(type_.element_type(), PlaintextType::Struct(Identifier::from_str("foo")?));
        assert_eq!(type_.length(), &U32::new(1));

        Ok(())
    }

    #[test]
    fn test_array_type_fails() -> Result<()> {
        let type_ = ArrayType::<CurrentNetwork>::from_str("[field; 0]");
        assert!(type_.is_err());

        let type_ = ArrayType::<CurrentNetwork>::from_str("[field; 4294967296]");
        assert!(type_.is_err());

        let type_ = ArrayType::<CurrentNetwork>::from_str("[foo; -1]");
        assert!(type_.is_err());

        Ok(())
    }
}
