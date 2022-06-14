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
        /// Prints the plaintext with visibility on every literal.
        fn fmt_plaintext_with_visibility<N: Network>(
            f: &mut Formatter,
            plaintext: &Plaintext<N>,
            visibility: &str,
        ) -> fmt::Result {
            match plaintext {
                // Prints the literal, i.e. 10field.public
                Plaintext::Literal(literal, ..) => write!(f, "{literal}.{visibility}"),
                // Prints the interface, i.e. { first: 10i64.private, second: 198u64.private }
                Plaintext::Interface(interface, ..) => {
                    let mut output = format!("{{ ");
                    for (identifier, plaintext) in interface.iter() {
                        output += &format!("{identifier}: {plaintext}.{visibility}, ");
                    }
                    output.pop(); // trailing space
                    output.pop(); // trailing comma
                    output += " }";
                    write!(f, "{output}")
                }
            }
        }

        match self {
            Self::Constant(constant) => fmt_plaintext_with_visibility(f, constant, "constant"),
            Self::Public(public) => fmt_plaintext_with_visibility(f, public, "public"),
            Self::Private(private) => fmt_plaintext_with_visibility(f, private, "private"),
        }
    }
}
