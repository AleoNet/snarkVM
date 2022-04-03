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

use crate::{variable_length::*, Identifier, Program};
use snarkvm_circuits::prelude::*;
use snarkvm_utilities::{error, FromBytes, ToBytes};

use core::{cmp::Ordering, fmt};
use std::io::{Read, Result as IoResult, Write};

pub type Locator = u64;

/// A register contains the location data to a value in memory.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Register<P: Program> {
    /// A register contains its locator in memory.
    Locator(Locator),
    /// A register member contains its locator and identifier in memory.
    Member(Locator, Identifier<P>),
}

impl<P: Program> Register<P> {
    /// Returns the locator of the register.
    #[inline]
    pub fn locator(&self) -> &Locator {
        match self {
            Self::Locator(locator) => locator,
            Self::Member(locator, _) => locator,
        }
    }
}

impl<P: Program> Parser for Register<P> {
    type Environment = P::Environment;

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
        let (string, identifier) = opt(pair(tag("."), Identifier::parse))(string)?;
        // Return the register.
        Ok((string, match identifier {
            Some((_, identifier)) => Self::Member(locator, identifier),
            None => Self::Locator(locator),
        }))
    }
}

impl<P: Program> fmt::Display for Register<P> {
    /// Prints the register as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Prints the register, i.e. r0
            Self::Locator(locator) => write!(f, "r{locator}"),
            // Prints the register member, i.e. r0.owner
            Self::Member(locator, identifier) => write!(f, "r{locator}.{identifier}"),
        }
    }
}

impl<P: Program> FromBytes for Register<P> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let variant = u8::read_le(&mut reader)?;
        let locator = read_variable_length_integer(&mut reader)?;
        match variant {
            0 => Ok(Self::Locator(locator)),
            1 => Ok(Self::Member(locator, Identifier::read_le(&mut reader)?)),
            2.. => Err(error(format!("Failed to deserialize register variant {variant}"))),
        }
    }
}

impl<P: Program> ToBytes for Register<P> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match self {
            Self::Locator(locator) => {
                u8::write_le(&0u8, &mut writer)?;
                variable_length_integer(locator).write_le(&mut writer)
            }
            Self::Member(locator, member) => {
                u8::write_le(&1u8, &mut writer)?;
                variable_length_integer(locator).write_le(&mut writer)?;
                member.write_le(&mut writer)
            }
        }
    }
}

impl<P: Program> Ord for Register<P> {
    /// Ordering is determined by the register locator (the identifier is ignored).
    fn cmp(&self, other: &Self) -> Ordering {
        self.locator().cmp(other.locator())
    }
}

impl<P: Program> PartialOrd for Register<P> {
    /// Ordering is determined by the register locator (the identifier is ignored).
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Process;

    type P = Process;

    #[test]
    fn test_register_display() {
        // Register::Locator
        assert_eq!("r0", format!("{}", Register::<P>::Locator(0)));
        assert_eq!("r1", format!("{}", Register::<P>::Locator(1)));
        assert_eq!("r2", format!("{}", Register::<P>::Locator(2)));
        assert_eq!("r3", format!("{}", Register::<P>::Locator(3)));
        assert_eq!("r4", format!("{}", Register::<P>::Locator(4)));

        // Register::Member
        assert_eq!("r0.owner", format!("{}", Register::<P>::Member(0, Identifier::from_str("owner"))));
        assert_eq!("r1.owner", format!("{}", Register::<P>::Member(1, Identifier::from_str("owner"))));
        assert_eq!("r2.owner", format!("{}", Register::<P>::Member(2, Identifier::from_str("owner"))));
        assert_eq!("r3.owner", format!("{}", Register::<P>::Member(3, Identifier::from_str("owner"))));
        assert_eq!("r4.owner", format!("{}", Register::<P>::Member(4, Identifier::from_str("owner"))));
    }

    #[test]
    fn test_register_partial_ord() {
        // Register::Locator
        assert_eq!(Some(Ordering::Equal), Register::<P>::Locator(0).partial_cmp(&Register::<P>::Locator(0)));
        assert_eq!(Some(Ordering::Less), Register::<P>::Locator(0).partial_cmp(&Register::<P>::Locator(1)));
        assert_eq!(Some(Ordering::Greater), Register::<P>::Locator(1).partial_cmp(&Register::<P>::Locator(0)));

        // Register::Member
        assert_eq!(
            Some(Ordering::Equal),
            Register::<P>::Member(0, Identifier::from_str("owner"))
                .partial_cmp(&Register::<P>::Member(0, Identifier::from_str("owner")))
        );
        assert_eq!(
            Some(Ordering::Less),
            Register::<P>::Member(0, Identifier::from_str("owner"))
                .partial_cmp(&Register::<P>::Member(1, Identifier::from_str("owner")))
        );
        assert_eq!(
            Some(Ordering::Greater),
            Register::<P>::Member(1, Identifier::from_str("owner"))
                .partial_cmp(&Register::<P>::Member(0, Identifier::from_str("owner")))
        );
    }

    #[test]
    fn test_register_eq() {
        // Register::Locator
        assert_eq!(Register::<P>::Locator(0), Register::<P>::Locator(0));
        assert_ne!(Register::<P>::Locator(0), Register::<P>::Locator(1));
        assert_ne!(Register::<P>::Locator(0), Register::<P>::Locator(2));
        assert_ne!(Register::<P>::Locator(0), Register::<P>::Locator(3));
        assert_ne!(Register::<P>::Locator(0), Register::<P>::Locator(4));

        // Register::Member
        assert_eq!(
            Register::<P>::Member(0, Identifier::from_str("owner")),
            Register::<P>::Member(0, Identifier::from_str("owner"))
        );
        assert_ne!(
            Register::<P>::Member(0, Identifier::from_str("owner")),
            Register::<P>::Member(1, Identifier::from_str("owner"))
        );
        assert_ne!(
            Register::<P>::Member(0, Identifier::from_str("owner")),
            Register::<P>::Member(2, Identifier::from_str("owner"))
        );
        assert_ne!(
            Register::<P>::Member(0, Identifier::from_str("owner")),
            Register::<P>::Member(3, Identifier::from_str("owner"))
        );
        assert_ne!(
            Register::<P>::Member(0, Identifier::from_str("owner")),
            Register::<P>::Member(4, Identifier::from_str("owner"))
        );
    }

    #[test]
    fn test_register_to_string() {
        // Register::Locator
        assert_eq!(Register::<P>::Locator(0).to_string(), "r0".to_string());
        assert_eq!(Register::<P>::Locator(1).to_string(), "r1".to_string());
        assert_eq!(Register::<P>::Locator(2).to_string(), "r2".to_string());
        assert_eq!(Register::<P>::Locator(3).to_string(), "r3".to_string());
        assert_eq!(Register::<P>::Locator(4).to_string(), "r4".to_string());

        // Register::Member
        assert_eq!(Register::<P>::Member(0, Identifier::from_str("owner")).to_string(), "r0.owner".to_string());
        assert_eq!(Register::<P>::Member(1, Identifier::from_str("owner")).to_string(), "r1.owner".to_string());
        assert_eq!(Register::<P>::Member(2, Identifier::from_str("owner")).to_string(), "r2.owner".to_string());
        assert_eq!(Register::<P>::Member(3, Identifier::from_str("owner")).to_string(), "r3.owner".to_string());
        assert_eq!(Register::<P>::Member(4, Identifier::from_str("owner")).to_string(), "r4.owner".to_string());
    }

    #[test]
    fn test_register_parse() {
        // Register::Locator
        assert_eq!(("", Register::<P>::Locator(0)), Register::parse("r0").unwrap());
        assert_eq!(("", Register::<P>::Locator(1)), Register::parse("r1").unwrap());
        assert_eq!(("", Register::<P>::Locator(2)), Register::parse("r2").unwrap());
        assert_eq!(("", Register::<P>::Locator(3)), Register::parse("r3").unwrap());
        assert_eq!(("", Register::<P>::Locator(4)), Register::parse("r4").unwrap());

        // Register::Member
        assert_eq!(("", Register::<P>::Member(0, Identifier::from_str("owner"))), Register::parse("r0.owner").unwrap());
        assert_eq!(("", Register::<P>::Member(1, Identifier::from_str("owner"))), Register::parse("r1.owner").unwrap());
        assert_eq!(("", Register::<P>::Member(2, Identifier::from_str("owner"))), Register::parse("r2.owner").unwrap());
        assert_eq!(("", Register::<P>::Member(3, Identifier::from_str("owner"))), Register::parse("r3.owner").unwrap());
        assert_eq!(("", Register::<P>::Member(4, Identifier::from_str("owner"))), Register::parse("r4.owner").unwrap());
    }

    #[test]
    fn test_register_parser_fails() {
        assert!(Register::<P>::parse("").is_err());
        assert!(Register::<P>::parse("r").is_err());
        // assert!(Register::<P>::parse("r0.owner.owner").is_err());
        // assert!(Register::<P>::parse("r0.owner.owner.owner").is_err());
        // assert!(Register::<P>::parse("r0.owner.owner.owner.owner").is_err());
        // assert!(Register::<P>::parse("r0.owner.owner.owner.owner.owner").is_err());
        // assert!(Register::<P>::parse("r0.owner.owner.owner.owner.owner.owner").is_err());
        // assert!(Register::<P>::parse("r0.owner.owner.owner.owner.owner.owner.owner").is_err());
        // assert!(Register::<P>::parse("r0.owner.owner.owner.owner.owner.owner.owner.owner").is_err());
    }
}
