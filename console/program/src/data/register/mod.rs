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
