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

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Checks that the given input value matches the layout of the value type.
    pub fn matches_value_type(&self, input: &Value<N>, value_type: &ValueType<N>) -> Result<()> {
        // Ensure the input value matches the declared type in the register.
        match (input, value_type) {
            (Value::Plaintext(plaintext), ValueType::Constant(plaintext_type))
            | (Value::Plaintext(plaintext), ValueType::Public(plaintext_type))
            | (Value::Plaintext(plaintext), ValueType::Private(plaintext_type)) => {
                self.matches_plaintext(plaintext, plaintext_type)
            }
            (Value::Record(record), ValueType::Record(record_name)) => self.matches_record(record, record_name),
            _ => bail!("Input value does not match the input register type '{value_type}'"),
        }
    }

    /// Checks that the given stack value matches the layout of the register type.
    pub fn matches_register_type(&self, stack_value: &Value<N>, register_type: &RegisterType<N>) -> Result<()> {
        match (stack_value, register_type) {
            (Value::Plaintext(plaintext), RegisterType::Plaintext(plaintext_type)) => {
                self.matches_plaintext(plaintext, plaintext_type)
            }
            (Value::Record(record), RegisterType::Record(record_name)) => self.matches_record(record, record_name),
            (Value::Record(record), RegisterType::ExternalRecord(locator)) => {
                self.matches_external_record(record, locator)
            }
            _ => bail!("Stack value does not match the register type '{register_type}'"),
        }
    }

    /// Checks that the given record matches the layout of the external record type.
    /// Note: Ordering for `owner` and `balance` **does** matter, however ordering
    /// for record data does **not** matter, as long as all defined members are present.
    pub fn matches_external_record(&self, record: &Record<N, Plaintext<N>>, locator: &Locator<N>) -> Result<()> {
        // Retrieve the record name.
        let record_name = locator.resource();

        // Ensure the record name is valid.
        ensure!(!Program::is_reserved_keyword(record_name), "Record name '{record_name}' is reserved");

        // Retrieve the record type from the program.
        let record_type = match self.get_external_record(locator) {
            Ok(record_type) => record_type,
            Err(..) => bail!("External '{locator}' is not defined in the program"),
        };

        // Ensure the record name matches.
        if record_type.name() != record_name {
            bail!("Expected external record '{record_name}', found external record '{}'", record_type.name())
        }

        self.matches_record_internal(record, &record_type, 0)
    }

    /// Checks that the given record matches the layout of the record type.
    /// Note: Ordering for `owner` and `balance` **does** matter, however ordering
    /// for record data does **not** matter, as long as all defined members are present.
    pub fn matches_record(&self, record: &Record<N, Plaintext<N>>, record_name: &Identifier<N>) -> Result<()> {
        // Ensure the record name is valid.
        ensure!(!Program::is_reserved_keyword(record_name), "Record name '{record_name}' is reserved");

        // Retrieve the record type from the program.
        let record_type = match self.program().get_record(record_name) {
            Ok(record_type) => record_type,
            Err(..) => bail!("Record '{record_name}' is not defined in the program"),
        };

        // Ensure the record name matches.
        if record_type.name() != record_name {
            bail!("Expected record '{record_name}', found record '{}'", record_type.name())
        }

        self.matches_record_internal(record, &record_type, 0)
    }

    /// Checks that the given plaintext matches the layout of the plaintext type.
    /// Note: Ordering does **not** matter, as long as all defined members are present.
    pub fn matches_plaintext(&self, plaintext: &Plaintext<N>, plaintext_type: &PlaintextType<N>) -> Result<()> {
        self.matches_plaintext_internal(plaintext, plaintext_type, 0)
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Checks that the given record matches the layout of the record type.
    /// Note: Ordering for `owner` and `balance` **does** matter, however ordering
    /// for record data does **not** matter, as long as all defined members are present.
    ///
    /// This method enforces `N::MAX_DATA_DEPTH` and `N::MAX_DATA_ENTRIES` limits.
    fn matches_record_internal(
        &self,
        record: &Record<N, Plaintext<N>>,
        record_type: &RecordType<N>,
        depth: usize,
    ) -> Result<()> {
        // If the depth exceeds the maximum depth, then the plaintext type is invalid.
        ensure!(depth <= N::MAX_DATA_DEPTH, "Plaintext exceeded maximum depth of {}", N::MAX_DATA_DEPTH);

        // Retrieve the record name.
        let record_name = record_type.name();

        // Ensure the number of record members does not exceed the maximum.
        let num_members = record.data().len();
        ensure!(num_members <= N::MAX_DATA_ENTRIES, "'{record_name}' cannot exceed {} entries", N::MAX_DATA_ENTRIES);

        // Ensure the number of interface members match.
        let num_expected_members = record_type.entries().len();
        if num_expected_members != num_members {
            bail!("'{record_name}' expected {num_expected_members} members, found {num_members} members")
        }

        // Ensure the visibility of the record owner matches the visibility in the record type.
        ensure!(
            record.owner().is_public() == record_type.owner().is_public(),
            "Record owner visibility does not match"
        );
        ensure!(
            record.owner().is_private() == record_type.owner().is_private(),
            "Record owner visibility does not match"
        );

        // Ensure the visibility of the record balance matches the visibility in the record type.
        ensure!(
            record.balance().is_public() == record_type.balance().is_public(),
            "Record balance visibility does not match"
        );
        ensure!(
            record.balance().is_private() == record_type.balance().is_private(),
            "Record balance visibility does not match"
        );

        // Ensure the record data matches the defined type.
        // Note: Ordering does **not** matter, as long as all defined members are present.
        for (expected_name, expected_type) in record_type.entries() {
            match record.data().iter().find(|(name, _)| *name == expected_name) {
                // Ensure the member type matches.
                Some((member_name, member_entry)) => {
                    // Ensure the member name is valid.
                    ensure!(!Program::is_reserved_keyword(member_name), "Member name '{member_name}' is reserved");
                    // Ensure the member value matches (recursive call).
                    self.matches_entry_internal(member_entry, expected_type, depth + 1)?
                }
                None => bail!("'{record_name}' is missing member '{expected_name}'"),
            }
        }
        Ok(())
    }

    /// Checks that the given entry matches the layout of the entry type.
    ///
    /// This method enforces `N::MAX_DATA_DEPTH` and `N::MAX_DATA_ENTRIES` limits.
    fn matches_entry_internal(
        &self,
        entry: &Entry<N, Plaintext<N>>,
        entry_type: &EntryType<N>,
        depth: usize,
    ) -> Result<()> {
        match (entry, entry_type) {
            (Entry::Constant(plaintext), EntryType::Constant(plaintext_type))
            | (Entry::Public(plaintext), EntryType::Public(plaintext_type))
            | (Entry::Private(plaintext), EntryType::Private(plaintext_type)) => {
                self.matches_plaintext_internal(plaintext, plaintext_type, depth)
            }
            _ => bail!("Invalid entry: function expected '{entry_type}'"),
        }
    }

    /// Checks that the given plaintext matches the layout of the plaintext type.
    /// Note: Ordering does **not** matter, as long as all defined members are present.
    ///
    /// This method enforces `N::MAX_DATA_DEPTH` and `N::MAX_DATA_ENTRIES` limits.
    fn matches_plaintext_internal(
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
                ensure!(!Program::is_reserved_keyword(interface_name), "Interface '{interface_name}' is reserved");

                // Retrieve the interface from the program.
                let interface = match self.program().get_interface(interface_name) {
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
                            ensure!(!Program::is_reserved_keyword(member_name), "Member '{member_name}' is reserved");
                            // Ensure the member plaintext matches (recursive call).
                            self.matches_plaintext_internal(member_plaintext, expected_type, depth + 1)?
                        }
                        None => bail!("'{interface_name}' is missing member '{expected_name}'"),
                    }
                }
                Ok(())
            }
        }
    }
}
