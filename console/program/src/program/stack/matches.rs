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

impl<N: Network> Stack<N> {
    /// Checks that `self` matches the layout of the plaintext type.
    /// Note: Ordering does **not** matter, as long as all defined members are present.
    pub fn matches(&self, plaintext: &Plaintext<N>, plaintext_type: &PlaintextType<N>) -> Result<()> {
        self.matches_internal(plaintext, plaintext_type, 0)
    }

    /// Checks that `self` matches the layout of the plaintext type.
    /// Note: Ordering does **not** matter, as long as all defined members are present.
    ///
    /// This method enforces `N::MAX_DATA_DEPTH` and `N::MAX_DATA_ENTRIES` limits.
    fn matches_internal(
        &self,
        plaintext: &Plaintext<N>,
        plaintext_type: &PlaintextType<N>,
        depth: usize,
    ) -> Result<()> {
        // If the depth exceeds the maximum depth, then the plaintext type is invalid.
        ensure!(depth <= N::MAX_DATA_DEPTH, "Plaintext exceeded maximum depth of {}", N::MAX_DATA_DEPTH);

        // Ensure the plaintext matches the plaintext definition in the program.
        match plaintext_type {
            PlaintextType::Literal(literal_type) => match plaintext {
                // If `plaintext` is a literal, it must match the literal type.
                Plaintext::Literal(literal, ..) => {
                    // Ensure the literal type matches.
                    match literal.to_type() == *literal_type {
                        true => Ok(()),
                        false => bail!("'{plaintext_type}' is invalid: expected {literal_type}, found {literal}"),
                    }
                }
                // If `plaintext` is an interface, this is a mismatch.
                Plaintext::Interface(..) => bail!("'{plaintext_type}' is invalid: expected literal, found interface"),
            },
            PlaintextType::Interface(interface_name) => {
                // Ensure the interface name is valid.
                ensure!(
                    !self.program.is_reserved_name(interface_name),
                    "Interface name '{interface_name}' is reserved"
                );

                // Retrieve the interface from the program.
                let interface = match self.program.get_interface(interface_name) {
                    Ok(interface) => interface,
                    Err(..) => bail!("Interface '{interface_name}' is not defined in the program"),
                };

                // Ensure the interface name matches.
                if interface.name() != interface_name {
                    bail!("Expected interface '{interface_name}', found interface '{}'", interface.name())
                }

                // Retrieve the interface members.
                let members = match plaintext {
                    Plaintext::Literal(..) => bail!("'{interface_name}' is invalid: expected interface, found literal"),
                    Plaintext::Interface(members, ..) => members,
                };

                // Ensure the number of interface members does not exceed the maximum.
                let num_members = members.len();
                ensure!(
                    num_members <= N::MAX_DATA_ENTRIES,
                    "'{interface_name}' cannot exceed {} entries",
                    N::MAX_DATA_ENTRIES
                );

                // Ensure the number of interface members match.
                let num_expected_members = interface.members().len();
                if num_expected_members != num_members {
                    bail!("'{interface_name}' expected {num_expected_members} members, found {num_members} members")
                }

                // Ensure the interface members match.
                // Note: Ordering does **not** matter, as long as all defined members are present.
                for (expected_name, expected_type) in interface.members() {
                    match members.iter().find(|(name, _)| *name == expected_name) {
                        // Ensure the member type matches.
                        Some((member_name, member_plaintext)) => {
                            // Ensure the member name is valid.
                            ensure!(
                                !self.program.is_reserved_name(member_name),
                                "Member name '{member_name}' is reserved"
                            );
                            // Ensure the member plaintext matches (recursive call).
                            self.matches_internal(member_plaintext, expected_type, depth + 1)?
                        }
                        None => bail!("'{interface_name}' is missing member '{expected_name}'",),
                    }
                }
                Ok(())
            }
        }
    }
}
