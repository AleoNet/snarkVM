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

use console::{network::prelude::*, program::PlaintextType};

/// A table input statement is of the form `input {plaintext_type}`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct TableInput<N: Network> {
    /// The table input type.
    type_: PlaintextType<N>,
}

impl<N: Network> TableInput<N> {
    /// Returns the key finalize type.
    #[inline]
    pub const fn type_(&self) -> &PlaintextType<N> {
        &self.type_
    }
}

impl<N: Network> TypeName for TableInput<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "input"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_key_type_name() -> Result<()> {
        assert_eq!(TableInput::<CurrentNetwork>::type_name(), "input");
        Ok(())
    }
}
