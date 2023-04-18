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

mod bytes;
mod parse;

use console::{
    network::prelude::*,
    program::{Identifier, PlaintextType},
};

/// An value statement is of the form `value {name} as {plaintext_type}.public;`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct MapValue<N: Network> {
    /// The value name.
    name: Identifier<N>,
    /// The value plaintext type.
    plaintext_type: PlaintextType<N>,
}

impl<N: Network> MapValue<N> {
    /// Returns the value name.
    #[inline]
    pub const fn name(&self) -> &Identifier<N> {
        &self.name
    }

    /// Returns the value plaintext type.
    #[inline]
    pub const fn plaintext_type(&self) -> &PlaintextType<N> {
        &self.plaintext_type
    }
}

impl<N: Network> TypeName for MapValue<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "value"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_value_type_name() {
        assert_eq!(MapValue::<CurrentNetwork>::type_name(), "value");
    }
}
