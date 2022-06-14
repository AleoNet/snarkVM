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

impl<N: Network> Debug for Entry<N, Plaintext<N>> {
    /// Prints the entry as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Entry<N, Plaintext<N>> {
    /// Prints the entry as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // TODO (howardwu): Handle how to print constant, public, and private visibility.
        match self {
            Self::Constant(constant) => write!(f, "{constant}"),
            Self::Public(public) => write!(f, "{public}"),
            Self::Private(private) => write!(f, "{private}"),
        }
    }
}
