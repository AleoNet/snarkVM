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

use console::{network::prelude::*, program::Identifier};

/// A program ID is of the form `{name}.{network}`.
/// If no `network`-level domain is specified, the default network is used.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct ProgramID<N: Network> {
    /// The program name.
    name: Identifier<N>,
    /// The network-level domain (NLD).
    network: Option<Identifier<N>>,
}

impl<N: Network> ProgramID<N> {
    /// Returns the program name.
    #[inline]
    pub const fn name(&self) -> &Identifier<N> {
        &self.name
    }

    /// Returns the network-level domain (NLD).
    #[inline]
    pub fn network(&self) -> Result<Identifier<N>> {
        match self.network {
            Some(network) => Ok(network),
            None => Identifier::from_str("aleo"),
        }
    }
}

impl<N: Network> Ord for ProgramID<N> {
    /// Ordering is determined by the network first, then the program name second.
    fn cmp(&self, other: &Self) -> Ordering {
        match self.network == other.network {
            true => self.name.to_string().cmp(&other.name.to_string()),
            false => match (self.network, other.network) {
                (Some(this), Some(that)) => this.to_string().cmp(&that.to_string()),
                (Some(this), None) => this.to_string().cmp(&"aleo".to_string()),
                (None, Some(that)) => "aleo".to_string().cmp(&that.to_string()),
                (None, None) => Ordering::Equal,
            },
        }
    }
}

impl<N: Network> PartialOrd for ProgramID<N> {
    /// Ordering is determined by the network first, then the program name second.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_partial_ord() -> Result<()> {
        let import1 = ProgramID::<CurrentNetwork>::from_str("bar.aleo")?;
        let import2 = ProgramID::<CurrentNetwork>::from_str("foo.aleo")?;

        let import3 = ProgramID::<CurrentNetwork>::from_str("bar.aleo")?;
        let import4 = ProgramID::<CurrentNetwork>::from_str("foo.aleo")?;

        assert_eq!(import1.partial_cmp(&import1), Some(Ordering::Equal));
        assert_eq!(import1.partial_cmp(&import2), Some(Ordering::Less));
        assert_eq!(import1.partial_cmp(&import3), Some(Ordering::Equal));
        assert_eq!(import1.partial_cmp(&import4), Some(Ordering::Less));

        assert_eq!(import2.partial_cmp(&import1), Some(Ordering::Greater));
        assert_eq!(import2.partial_cmp(&import2), Some(Ordering::Equal));
        assert_eq!(import2.partial_cmp(&import3), Some(Ordering::Greater));
        assert_eq!(import2.partial_cmp(&import4), Some(Ordering::Equal));

        assert_eq!(import3.partial_cmp(&import1), Some(Ordering::Equal));
        assert_eq!(import3.partial_cmp(&import2), Some(Ordering::Less));
        assert_eq!(import3.partial_cmp(&import3), Some(Ordering::Equal));
        assert_eq!(import3.partial_cmp(&import4), Some(Ordering::Less));

        assert_eq!(import4.partial_cmp(&import1), Some(Ordering::Greater));
        assert_eq!(import4.partial_cmp(&import2), Some(Ordering::Equal));
        assert_eq!(import4.partial_cmp(&import3), Some(Ordering::Greater));
        assert_eq!(import4.partial_cmp(&import4), Some(Ordering::Equal));

        Ok(())
    }
}
