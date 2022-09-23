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
    program::{Register, RegisterType},
};

/// An output statement defines an output of a function, and may refer to the register
/// in either a register or a register member. An output statement is of the form
/// `output {register} as {register_type};`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Output<N: Network> {
    /// The output register.
    register: Register<N>,
    /// The output register type.
    register_type: RegisterType<N>,
}

impl<N: Network> Output<N> {
    /// Returns the output register.
    #[inline]
    pub const fn register(&self) -> &Register<N> {
        &self.register
    }

    /// Returns the output register type.
    #[inline]
    pub const fn register_type(&self) -> &RegisterType<N> {
        &self.register_type
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
