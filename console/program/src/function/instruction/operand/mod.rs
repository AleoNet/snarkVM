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

use crate::{Literal, Register, Value};
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
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

impl<N: Network> Operand<N> {
    /// Returns `true` if the operand is a literal.
    #[inline]
    pub const fn is_literal(&self) -> bool {
        matches!(self, Operand::Literal(_))
    }

    /// Returns `true` if the operand is a register.
    #[inline]
    pub const fn is_register(&self) -> bool {
        matches!(self, Operand::Register(_))
    }
}

impl<N: Network> Parser for Operand<N> {
    /// Parses a string into a operand.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse to determine the operand (order matters).
        alt((
            map(Literal::parse, |literal| Self::Literal(literal)),
            map(Register::parse, |register| Self::Register(register)),
        ))(string)
    }
}

impl<N: Network> FromStr for Operand<N> {
    type Err = Error;

    /// Parses a string into an operand.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for Operand<N> {
    /// Prints the operand as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Operand<N> {
    /// Prints the operand as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            // Prints the literal, i.e. 10field.private
            Self::Literal(literal) => Display::fmt(literal, f),
            // Prints the register, i.e. r0 or r0.owner
            Self::Register(register) => Display::fmt(register, f),
        }
    }
}

impl<N: Network> FromBytes for Operand<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        match u8::read_le(&mut reader) {
            Ok(0) => Ok(Self::Literal(Literal::read_le(&mut reader)?)),
            Ok(1) => Ok(Self::Register(Register::read_le(&mut reader)?)),
            Ok(variant) => Err(error(format!("Failed to deserialize operand variant {variant}"))),
            Err(err) => Err(err),
        }
    }
}

impl<N: Network> ToBytes for Operand<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Literal(literal) => {
                u8::write_le(&0u8, &mut writer)?;
                literal.write_le(&mut writer)
            }
            Self::Register(register) => {
                u8::write_le(&1u8, &mut writer)?;
                register.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_operand_from_literal() -> Result<()> {
        let literal = Literal::from_str("1field")?;
        let expected = Operand::<CurrentNetwork>::Literal(literal.clone());

        let operand = Operand::<CurrentNetwork>::from(literal);
        assert_eq!(expected, operand);
        assert!(operand.is_literal());
        assert!(!operand.is_register());
        Ok(())
    }

    #[test]
    fn test_operand_from_register() -> Result<()> {
        let register = Register::from_str("r0")?;
        let expected = Operand::<CurrentNetwork>::Register(register.clone());

        let operand = Operand::<CurrentNetwork>::from(register);
        assert_eq!(expected, operand);
        assert!(!operand.is_literal());
        assert!(operand.is_register());
        Ok(())
    }

    #[test]
    fn test_operand_from_register_member() -> Result<()> {
        let register = Register::from_str("r0.owner")?;
        let expected = Operand::<CurrentNetwork>::Register(register.clone());

        let operand = Operand::<CurrentNetwork>::from(register);
        assert_eq!(expected, operand);
        assert!(!operand.is_literal());
        assert!(operand.is_register());
        Ok(())
    }

    #[test]
    fn test_operand_parse() -> Result<()> {
        let operand = Operand::<CurrentNetwork>::parse("1field").unwrap().1;
        assert_eq!(Operand::Literal(Literal::from_str("1field")?), operand);
        assert!(operand.is_literal());
        assert!(!operand.is_register());

        let operand = Operand::<CurrentNetwork>::parse("r0").unwrap().1;
        assert_eq!(Operand::Register(Register::from_str("r0")?), operand);
        assert!(!operand.is_literal());
        assert!(operand.is_register());

        let operand = Operand::<CurrentNetwork>::parse("r0.owner").unwrap().1;
        assert_eq!(Operand::Register(Register::from_str("r0.owner")?), operand);
        assert!(!operand.is_literal());
        assert!(operand.is_register());

        // Sanity check a failure case.
        let (remainder, operand) = Operand::<CurrentNetwork>::parse("1field.private").unwrap();
        assert_eq!(Operand::Literal(Literal::from_str("1field")?), operand);
        assert_eq!(".private", remainder);

        Ok(())
    }

    #[test]
    fn test_operand_display() {
        let operand = Operand::<CurrentNetwork>::parse("1field").unwrap().1;
        assert_eq!(format!("{operand}"), "1field");

        let operand = Operand::<CurrentNetwork>::parse("r0").unwrap().1;
        assert_eq!(format!("{operand}"), "r0");

        let operand = Operand::<CurrentNetwork>::parse("r0.owner").unwrap().1;
        assert_eq!(format!("{operand}"), "r0.owner");
    }

    #[test]
    fn test_operand_from_str_fails() -> Result<()> {
        assert!(Operand::<CurrentNetwork>::from_str("1field.private").is_err());
        Ok(())
    }
}
