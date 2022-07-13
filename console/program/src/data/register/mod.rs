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
mod serialize;

use crate::Identifier;
use snarkvm_console_network::prelude::*;

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
    pub const fn locator(&self) -> u64 {
        match self {
            Self::Locator(locator) => *locator,
            Self::Member(locator, _) => *locator,
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
}
