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

use super::*;

impl<N: Network> Parser for Operand<N> {
    /// Parses a string into a operand.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse to determine the operand (order matters).
        alt((
            map(Literal::parse, |literal| Self::Literal(literal)),
            map(Register::parse, |register| Self::Register(register)),
            map(tag("self.caller"), |_| Self::Caller),
            map(ProgramID::parse, |program_id| Self::ProgramID(program_id)),
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
            // Prints the program ID, i.e. howard.aleo
            Self::ProgramID(program_id) => Display::fmt(program_id, f),
            // Prints the caller, i.e. self.caller
            Self::Caller => write!(f, "self.caller"),
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

        let operand = Operand::<CurrentNetwork>::parse("howard.aleo").unwrap().1;
        assert_eq!(Operand::ProgramID(ProgramID::from_str("howard.aleo")?), operand);

        let operand = Operand::<CurrentNetwork>::parse("self.caller").unwrap().1;
        assert_eq!(Operand::Caller, operand);

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

        let operand = Operand::<CurrentNetwork>::parse("howard.aleo").unwrap().1;
        assert_eq!(format!("{operand}"), "howard.aleo");

        let operand = Operand::<CurrentNetwork>::parse("self.caller").unwrap().1;
        assert_eq!(format!("{operand}"), "self.caller");
    }

    #[test]
    fn test_operand_from_str_fails() -> Result<()> {
        assert!(Operand::<CurrentNetwork>::from_str("1field.private").is_err());
        Ok(())
    }
}
