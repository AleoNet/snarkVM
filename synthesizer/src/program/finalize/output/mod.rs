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

use crate::Operand;

use console::{network::prelude::*, program::PlaintextType};

/// An output statement defines an output of finalize.
/// An output statement is of the form `output {operand} as {plaintext_type}.public;`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Output<N: Network> {
    /// The output operand.
    operand: Operand<N>,
    /// The output plaintext type.
    plaintext_type: PlaintextType<N>,
}

impl<N: Network> Output<N> {
    /// Returns the output operand.
    #[inline]
    pub const fn operand(&self) -> &Operand<N> {
        &self.operand
    }

    /// Returns the output finalize type.
    #[inline]
    pub const fn plaintext_type(&self) -> &PlaintextType<N> {
        &self.plaintext_type
    }
}

impl<N: Network> TypeName for Output<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "output"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_output_type_name() {
        assert_eq!(Output::<CurrentNetwork>::type_name(), "output");
    }
}
