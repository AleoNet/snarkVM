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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]

use crate::Identifier;
use snarkvm_console_network::prelude::*;
use snarkvm_utilities::{
    error,
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

/// A register contains the location data to a value in memory.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Register<N: Network> {
    /// A register contains its locator in memory.
    Locator(u64),
    /// A register member contains its locator and identifier(s) in memory.
    Member(u64, Vec<Identifier<N>>),
}

impl<N: Network> Register<N> {
    /// Returns the locator of the register.
    #[inline]
    pub fn locator(&self) -> u64 {
        match self {
            Self::Locator(locator) => *locator,
            Self::Member(locator, _) => *locator,
        }
    }
}

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
                // Ensure the number of identifiers is within `N::MAX_DATA_DEPTH`.
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

impl<N: Network> FromBytes for Register<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        let locator = read_variable_length_integer(&mut reader)?;
        match variant {
            0 => Ok(Self::Locator(locator)),
            1 => {
                // Read the number of identifiers.
                let num_identifiers = u16::read_le(&mut reader)?;
                // Read the identifiers.
                let mut identifiers = Vec::with_capacity(num_identifiers as usize);
                for _ in 0..num_identifiers {
                    identifiers.push(Identifier::read_le(&mut reader)?);
                }
                Ok(Self::Member(locator, identifiers))
            }
            2.. => Err(error(format!("Failed to deserialize register variant {variant}"))),
        }
    }
}

impl<N: Network> ToBytes for Register<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Locator(locator) => {
                u8::write_le(&0u8, &mut writer)?;
                variable_length_integer(locator).write_le(&mut writer)
            }
            Self::Member(locator, identifiers) => {
                // Ensure the number of identifiers is within `N::MAX_DATA_DEPTH`.
                if identifiers.len() > N::MAX_DATA_DEPTH {
                    return Err(error("Failed to serialize register: too many identifiers"));
                }

                u8::write_le(&1u8, &mut writer)?;
                variable_length_integer(locator).write_le(&mut writer)?;
                (identifiers.len() as u16).write_le(&mut writer)?;
                identifiers.write_le(&mut writer)
            }
        }
    }
}

impl<N: Network> Ord for Register<N> {
    /// Ordering is determined by the register locator (any member identifiers are ignored).
    fn cmp(&self, other: &Self) -> Ordering {
        self.locator().cmp(&other.locator())
    }
}

impl<N: Network> PartialOrd for Register<N> {
    /// Ordering is determined by the register locator (any member identifiers are ignored).
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
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
        assert_eq!("r0", format!("{}", Register::<CurrentNetwork>::Locator(0)));
        assert_eq!("r1", format!("{}", Register::<CurrentNetwork>::Locator(1)));
        assert_eq!("r2", format!("{}", Register::<CurrentNetwork>::Locator(2)));
        assert_eq!("r3", format!("{}", Register::<CurrentNetwork>::Locator(3)));
        assert_eq!("r4", format!("{}", Register::<CurrentNetwork>::Locator(4)));

        // Register::Member
        assert_eq!(
            "r0.owner",
            format!("{}", Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?]))
        );
        assert_eq!(
            "r1.owner",
            format!("{}", Register::<CurrentNetwork>::Member(1, vec![Identifier::from_str("owner")?]))
        );
        assert_eq!(
            "r2.owner",
            format!("{}", Register::<CurrentNetwork>::Member(2, vec![Identifier::from_str("owner")?]))
        );
        assert_eq!(
            "r3.owner",
            format!("{}", Register::<CurrentNetwork>::Member(3, vec![Identifier::from_str("owner")?]))
        );
        assert_eq!(
            "r4.owner",
            format!("{}", Register::<CurrentNetwork>::Member(4, vec![Identifier::from_str("owner")?]))
        );
        Ok(())
    }

    #[test]
    fn test_register_partial_ord() -> Result<()> {
        // Register::Locator
        assert_eq!(
            Some(Ordering::Equal),
            Register::<CurrentNetwork>::Locator(0).partial_cmp(&Register::<CurrentNetwork>::Locator(0))
        );
        assert_eq!(
            Some(Ordering::Less),
            Register::<CurrentNetwork>::Locator(0).partial_cmp(&Register::<CurrentNetwork>::Locator(1))
        );
        assert_eq!(
            Some(Ordering::Greater),
            Register::<CurrentNetwork>::Locator(1).partial_cmp(&Register::<CurrentNetwork>::Locator(0))
        );

        // Register::Member
        assert_eq!(
            Some(Ordering::Equal),
            Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?]).partial_cmp(&Register::<
                CurrentNetwork,
            >::Member(
                0,
                vec![Identifier::from_str("owner")?]
            ))
        );
        assert_eq!(
            Some(Ordering::Less),
            Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?]).partial_cmp(&Register::<
                CurrentNetwork,
            >::Member(
                1,
                vec![Identifier::from_str("owner")?]
            ))
        );
        assert_eq!(
            Some(Ordering::Greater),
            Register::<CurrentNetwork>::Member(1, vec![Identifier::from_str("owner")?]).partial_cmp(&Register::<
                CurrentNetwork,
            >::Member(
                0,
                vec![Identifier::from_str("owner")?]
            ))
        );
        Ok(())
    }

    #[test]
    fn test_register_eq() -> Result<()> {
        // Register::Locator
        assert_eq!(Register::<CurrentNetwork>::Locator(0), Register::<CurrentNetwork>::Locator(0));
        assert_ne!(Register::<CurrentNetwork>::Locator(0), Register::<CurrentNetwork>::Locator(1));
        assert_ne!(Register::<CurrentNetwork>::Locator(0), Register::<CurrentNetwork>::Locator(2));
        assert_ne!(Register::<CurrentNetwork>::Locator(0), Register::<CurrentNetwork>::Locator(3));
        assert_ne!(Register::<CurrentNetwork>::Locator(0), Register::<CurrentNetwork>::Locator(4));

        // Register::Member
        assert_eq!(
            Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?]),
            Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?])
        );
        assert_ne!(
            Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?]),
            Register::<CurrentNetwork>::Member(1, vec![Identifier::from_str("owner")?])
        );
        assert_ne!(
            Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?]),
            Register::<CurrentNetwork>::Member(2, vec![Identifier::from_str("owner")?])
        );
        assert_ne!(
            Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?]),
            Register::<CurrentNetwork>::Member(3, vec![Identifier::from_str("owner")?])
        );
        assert_ne!(
            Register::<CurrentNetwork>::Member(0, vec![Identifier::from_str("owner")?]),
            Register::<CurrentNetwork>::Member(4, vec![Identifier::from_str("owner")?])
        );
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
