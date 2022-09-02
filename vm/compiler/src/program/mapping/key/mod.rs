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

mod bytes;
mod parse;

use console::{
    network::prelude::*,
    program::{FinalizeType, Identifier},
};

/// A key statement is of the form `key {name} as {register_type}`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct MapKey<N: Network> {
    /// The key name.
    name: Identifier<N>,
    /// The key finalize type.
    finalize_type: FinalizeType<N>,
}

impl<N: Network> MapKey<N> {
    /// Returns the key name.
    #[inline]
    pub const fn name(&self) -> &Identifier<N> {
        &self.name
    }

    /// Returns the key finalize type.
    #[inline]
    pub const fn finalize_type(&self) -> &FinalizeType<N> {
        &self.finalize_type
    }
}

impl<N: Network> TypeName for MapKey<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "key"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_key_type_name() -> Result<()> {
        assert_eq!(MapKey::<CurrentNetwork>::type_name(), "key");
        Ok(())
    }
}
