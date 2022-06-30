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

use super::*;

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

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_operand_parse() -> Result<()> {
        let operand = Operand::<CurrentNetwork>::parse("1field").unwrap().1;
        assert_eq!(Operand::Literal(Literal::from_str("1field")?), operand);

        let operand = Operand::<CurrentNetwork>::parse("r0").unwrap().1;
        assert_eq!(Operand::Register(Register::from_str("r0")?), operand);

        let operand = Operand::<CurrentNetwork>::parse("r0.owner").unwrap().1;
        assert_eq!(Operand::Register(Register::from_str("r0.owner")?), operand);

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
