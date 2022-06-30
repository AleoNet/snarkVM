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
    program::{Literal, Register},
};

/// The `Operand` enum represents the options for an operand in an instruction.
/// This enum is designed to for instructions such as `add {Register} {Literal} into {Register}`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Operand<N: Network> {
    /// The operand is a literal.
    Literal(Literal<N>),
    /// The operand is a register.
    Register(Register<N>),
}

impl<N: Network> From<Literal<N>> for Operand<N> {
    /// Initializes a new operand from a literal.
    #[inline]
    fn from(literal: Literal<N>) -> Self {
        Operand::Literal(literal)
    }
}

impl<N: Network> From<&Literal<N>> for Operand<N> {
    /// Initializes a new operand from a reference to a literal.
    #[inline]
    fn from(literal: &Literal<N>) -> Self {
        Operand::Literal(literal.clone())
    }
}

impl<N: Network> From<Register<N>> for Operand<N> {
    /// Initializes a new operand from a register.
    #[inline]
    fn from(register: Register<N>) -> Self {
        Operand::Register(register)
    }
}

impl<N: Network> From<&Register<N>> for Operand<N> {
    /// Initializes a new operand from a reference to a register.
    #[inline]
    fn from(register: &Register<N>) -> Self {
        Operand::Register(register.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_operand_from_literal() -> Result<()> {
        let literal = Literal::from_str("1field")?;
        let expected = Operand::<CurrentNetwork>::Literal(literal.clone());

        let operand = Operand::<CurrentNetwork>::from(literal);
        assert_eq!(expected, operand);
        Ok(())
    }

    #[test]
    fn test_operand_from_register() -> Result<()> {
        let register = Register::from_str("r0")?;
        let expected = Operand::<CurrentNetwork>::Register(register.clone());

        let operand = Operand::<CurrentNetwork>::from(register);
        assert_eq!(expected, operand);
        Ok(())
    }

    #[test]
    fn test_operand_from_register_member() -> Result<()> {
        let register = Register::from_str("r0.owner")?;
        let expected = Operand::<CurrentNetwork>::Register(register.clone());

        let operand = Operand::<CurrentNetwork>::from(register);
        assert_eq!(expected, operand);
        Ok(())
    }
}
