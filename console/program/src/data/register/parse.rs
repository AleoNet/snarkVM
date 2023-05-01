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

use super::*;

impl<N: Network> Parser for Register<N> {
    /// Parses a string into a register.
    /// The register is of the form `r{locator}` or `r{locator}.{identifier}`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the register character from the string.
        let (string, _) = tag("r")(string)?;
        // Parse the locator from the string.
        let (string, locator) =
            map_res(recognize(many1(one_of("0123456789"))), |locator: &str| locator.parse::<u64>())(string)?;
        // Parse the identifier from the string, if it is a register member.
        let (string, identifiers): (&str, Vec<Identifier<N>>) =
            map_res(many0(pair(tag("."), Identifier::parse)), |identifiers| {
                // Ensure the number of identifiers is within the limit.
                if identifiers.len() <= N::MAX_DATA_DEPTH {
                    Ok(identifiers.iter().cloned().map(|(_, identifier)| identifier).collect())
                } else {
                    Err(error(format!("Register \'r{locator}\' has too many identifiers ({})", identifiers.len())))
                }
            })(string)?;
        // Return the register.
        Ok((string, match identifiers.len() {
            0 => Self::Locator(locator),
            _ => Self::Member(locator, identifiers),
        }))
    }
}

impl<N: Network> FromStr for Register<N> {
    type Err = Error;

    /// Parses a string into a register.
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

impl<N: Network> Debug for Register<N> {
    /// Prints the register as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Register<N> {
    /// Prints the register as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            // Prints the register, i.e. r0
            Self::Locator(locator) => write!(f, "r{locator}"),
            // Prints the register member, i.e. r0.owner
            Self::Member(locator, identifiers) => {
                write!(f, "r{locator}")?;
                for identifier in identifiers {
                    write!(f, ".{identifier}")?;
                }
                Ok(())
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
    fn test_register_display() -> Result<()> {
        // Register::Locator
        assert_eq!("r0", Register::<CurrentNetwork>::Locator(0).to_string());
        assert_eq!("r1", Register::<CurrentNetwork>::Locator(1).to_string());
        assert_eq!("r2", Register::<CurrentNetwork>::Locator(2).to_string());
        assert_eq!("r3", Register::<CurrentNetwork>::Locator(3).to_string());
        assert_eq!("r4", Register::<CurrentNetwork>::Locator(4).to_string());

        // Register::Member
        assert_eq!("r0.owner", Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?]).to_string());
        assert_eq!("r1.owner", Register::<CurrentNetwork>::Member(1, vec![Identifier::from_str("owner")?]).to_string());
        assert_eq!("r2.owner", Register::<CurrentNetwork>::Member(2, vec![Identifier::from_str("owner")?]).to_string());
        assert_eq!("r3.owner", Register::<CurrentNetwork>::Member(3, vec![Identifier::from_str("owner")?]).to_string());
        assert_eq!("r4.owner", Register::<CurrentNetwork>::Member(4, vec![Identifier::from_str("owner")?]).to_string());
        Ok(())
    }

    #[test]
    fn test_register_to_string() -> Result<()> {
        // Register::Locator
        assert_eq!(Register::<CurrentNetwork>::Locator(0).to_string(), "r0".to_string());
        assert_eq!(Register::<CurrentNetwork>::Locator(1).to_string(), "r1".to_string());
        assert_eq!(Register::<CurrentNetwork>::Locator(2).to_string(), "r2".to_string());
        assert_eq!(Register::<CurrentNetwork>::Locator(3).to_string(), "r3".to_string());
        assert_eq!(Register::<CurrentNetwork>::Locator(4).to_string(), "r4".to_string());

        // Register::Member
        assert_eq!(
            Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?]).to_string(),
            "r0.owner".to_string()
        );
        assert_eq!(
            Register::<CurrentNetwork>::Member(1, vec![Identifier::from_str("owner")?]).to_string(),
            "r1.owner".to_string()
        );
        assert_eq!(
            Register::<CurrentNetwork>::Member(2, vec![Identifier::from_str("owner")?]).to_string(),
            "r2.owner".to_string()
        );
        assert_eq!(
            Register::<CurrentNetwork>::Member(3, vec![Identifier::from_str("owner")?]).to_string(),
            "r3.owner".to_string()
        );
        assert_eq!(
            Register::<CurrentNetwork>::Member(4, vec![Identifier::from_str("owner")?]).to_string(),
            "r4.owner".to_string()
        );
        Ok(())
    }

    #[test]
    fn test_register_parse() -> Result<()> {
        // Register::Locator
        assert_eq!(("", Register::<CurrentNetwork>::Locator(0)), Register::parse("r0").unwrap());
        assert_eq!(("", Register::<CurrentNetwork>::Locator(1)), Register::parse("r1").unwrap());
        assert_eq!(("", Register::<CurrentNetwork>::Locator(2)), Register::parse("r2").unwrap());
        assert_eq!(("", Register::<CurrentNetwork>::Locator(3)), Register::parse("r3").unwrap());
        assert_eq!(("", Register::<CurrentNetwork>::Locator(4)), Register::parse("r4").unwrap());

        // Register::Member
        assert_eq!(
            ("", Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?])),
            Register::parse("r0.owner").unwrap()
        );
        assert_eq!(
            ("", Register::<CurrentNetwork>::Member(1, vec![Identifier::from_str("owner")?])),
            Register::parse("r1.owner").unwrap()
        );
        assert_eq!(
            ("", Register::<CurrentNetwork>::Member(2, vec![Identifier::from_str("owner")?])),
            Register::parse("r2.owner").unwrap()
        );
        assert_eq!(
            ("", Register::<CurrentNetwork>::Member(3, vec![Identifier::from_str("owner")?])),
            Register::parse("r3.owner").unwrap()
        );
        assert_eq!(
            ("", Register::<CurrentNetwork>::Member(4, vec![Identifier::from_str("owner")?])),
            Register::parse("r4.owner").unwrap()
        );

        // Register::Member with multiple identifiers
        for i in 1..=CurrentNetwork::MAX_DATA_DEPTH {
            let mut string = "r0.".to_string();
            for _ in 0..i {
                string.push_str("owner.");
            }
            string.pop(); // Remove last '.'

            assert_eq!(
                ("", Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?; i])),
                Register::<CurrentNetwork>::parse(&string).unwrap()
            );
        }

        Ok(())
    }

    #[test]
    fn test_register_parser_fails() {
        assert!(Register::<CurrentNetwork>::parse("").is_err());
        assert!(Register::<CurrentNetwork>::parse("r").is_err());

        // Register::Member with multiple identifiers that exceed the maximum depth.
        for i in CurrentNetwork::MAX_DATA_DEPTH + 1..CurrentNetwork::MAX_DATA_DEPTH * 2 {
            let mut string = "r0.".to_string();
            for _ in 0..i {
                string.push_str("owner.");
            }
            string.pop(); // Remove last '.'

            assert!(Register::<CurrentNetwork>::parse(&string).is_err());
        }
    }
}
