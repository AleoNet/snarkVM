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

use crate::ElementType;
use snarkvm_console_network::prelude::*;

use core::fmt::{Debug, Display};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct VectorType<N: Network> {
    /// The type of the elements in the vector.
    element_type: ElementType<N>,
}

impl<N: Network> VectorType<N> {
    /// Constructs a new vector type.
    pub fn new(element_type: ElementType<N>) -> Self {
        Self { element_type }
    }

    /// Returns the element type.
    pub fn element_type(&self) -> &ElementType<N> {
        &self.element_type
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    use crate::{Identifier, LiteralType};
    use core::str::FromStr;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_vector_type() -> Result<()> {
        // Test literal vector types.
        let type_ = VectorType::<CurrentNetwork>::from_str("[field]")?;
        assert_eq!(type_, VectorType::<CurrentNetwork>::new(ElementType::from(LiteralType::Field)));
        assert_eq!(
            type_.to_bytes_le()?,
            VectorType::<CurrentNetwork>::from_bytes_le(&type_.to_bytes_le()?)?.to_bytes_le()?
        );
        assert_eq!(type_.element_type(), &ElementType::from(LiteralType::Field));

        // Test struct vector types.
        let type_ = VectorType::<CurrentNetwork>::from_str("[foo]")?;
        assert_eq!(type_, VectorType::<CurrentNetwork>::new(ElementType::from(Identifier::from_str("foo")?)));
        assert_eq!(
            type_.to_bytes_le()?,
            VectorType::<CurrentNetwork>::from_bytes_le(&type_.to_bytes_le()?)?.to_bytes_le()?
        );
        assert_eq!(type_.element_type(), &ElementType::from(Identifier::from_str("foo")?));

        // Test vector type with maximum length.
        let type_ = VectorType::<CurrentNetwork>::from_str("[scalar]")?;
        assert_eq!(type_, VectorType::<CurrentNetwork>::new(ElementType::from(LiteralType::Scalar)));
        assert_eq!(
            type_.to_bytes_le()?,
            VectorType::<CurrentNetwork>::from_bytes_le(&type_.to_bytes_le()?)?.to_bytes_le()?
        );
        assert_eq!(type_.element_type(), &ElementType::from(LiteralType::Scalar));

        Ok(())
    }

    #[test]
    fn test_vector_type_fails() -> Result<()> {
        let type_ = VectorType::<CurrentNetwork>::from_str("[[field]]");
        assert!(type_.is_err());

        let type_ = VectorType::<CurrentNetwork>::from_str("[[foo]]");
        assert!(type_.is_err());

        let type_ = VectorType::<CurrentNetwork>::from_str("[field; 3]");
        assert!(type_.is_err());

        let type_ = VectorType::<CurrentNetwork>::from_str("[foo; -1]");
        assert!(type_.is_err());

        Ok(())
    }
}
