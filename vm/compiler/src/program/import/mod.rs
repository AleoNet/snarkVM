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
    program::{Identifier, ProgramID},
};

/// An import statement defines an imported program, and is of the form `import {name}.{network};`.
/// If no `network`-level domain is specified, the default network is used.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Import<N: Network> {
    /// The imported program ID.
    program_id: ProgramID<N>,
}

impl<N: Network> Import<N> {
    /// Returns the imported program ID.
    #[inline]
    pub const fn program_id(&self) -> &ProgramID<N> {
        &self.program_id
    }

    /// Returns the imported program name.
    #[inline]
    pub const fn name(&self) -> &Identifier<N> {
        self.program_id.name()
    }

    /// Returns the imported network-level domain (NLD).
    #[inline]
    pub const fn network(&self) -> &Identifier<N> {
        self.program_id.network()
    }
}

impl<N: Network> TypeName for Import<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "import"
    }
}

impl<N: Network> Ord for Import<N> {
    /// Ordering is determined by the NLD first, then the program name second.
    fn cmp(&self, other: &Self) -> Ordering {
        self.program_id.cmp(&other.program_id)
    }
}

impl<N: Network> PartialOrd for Import<N> {
    /// Ordering is determined by the NLD first, then the program name second.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.program_id.partial_cmp(&other.program_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_import_type_name() -> Result<()> {
        assert_eq!(Import::<CurrentNetwork>::type_name(), "import");
        Ok(())
    }

    #[test]
    fn test_import_partial_ord() -> Result<()> {
        let import1 = Import::<CurrentNetwork>::from_str("import bar.aleo;")?;
        let import2 = Import::<CurrentNetwork>::from_str("import foo.aleo;")?;

        let import3 = Import::<CurrentNetwork>::from_str("import bar.aleo;")?;
        let import4 = Import::<CurrentNetwork>::from_str("import foo.aleo;")?;

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
