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

use console::{network::prelude::*, program::Literal};

// TODO (d0cd): Consider allowing PlaintextTypes.
/// A table entry statement, e.g `entry 1field 2field to 3field;`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Entry<N: Network> {
    pub inputs: Vec<Literal<N>>,
    pub outputs: Vec<Literal<N>>,
}

impl<N: Network> Entry<N> {
    /// Returns the inputs of the entry.
    #[inline]
    pub fn inputs(&self) -> &[Literal<N>] {
        &self.inputs
    }

    /// Returns the outputs of the entry.
    #[inline]
    pub fn outputs(&self) -> &[Literal<N>] {
        &self.outputs
    }
}

impl<N: Network> TypeName for Entry<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "entry"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_key_type_name() -> Result<()> {
        assert_eq!(Entry::<CurrentNetwork>::type_name(), "entry");
        Ok(())
    }
}
