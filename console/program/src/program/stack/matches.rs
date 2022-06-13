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
    /// Checks that the given input value matches the layout of the value type.
    pub fn matches_input(&self, input: &Input<N>, value_type: &ValueType<N>) -> Result<()> {
        // Ensure the input value matches the declared type in the register.
        match (input, value_type) {
            (Input::Plaintext(plaintext), ValueType::Constant(plaintext_type))
            | (Input::Plaintext(plaintext), ValueType::Public(plaintext_type))
            | (Input::Plaintext(plaintext), ValueType::Private(plaintext_type)) => {
                self.matches_plaintext(plaintext, &plaintext_type)
            }
            (Input::Record(record), ValueType::Record(record_name)) => self.matches_record(record, &record_name),
            _ => bail!("Input value does not match the input register type '{value_type}'"),
        }
    }

    /// Checks that the given register value matches the layout of the register type.
    pub fn matches_register(&self, register_value: &RegisterValue<N>, register_type: &RegisterType<N>) -> Result<()> {
        match (register_value, register_type) {
            (RegisterValue::Plaintext(plaintext), RegisterType::Plaintext(plaintext_type)) => {
                self.matches_plaintext(plaintext, &plaintext_type)
            }
            (RegisterValue::Record(record), RegisterType::Record(record_name)) => {
                self.matches_record(record, &record_name)
            }
            _ => bail!("Register value does not match the register type '{register_type}'"),
        }
    }

    /// Checks that the given value matches the layout of the value type.
    pub fn matches_value(&self, value: &Value<N, Plaintext<N>>, value_type: &ValueType<N>) -> Result<()> {
        self.matches_value_internal(value, value_type, 0)
    }

    /// Checks that the given record matches the layout of the record type.
    /// Note: Ordering for `owner` and `balance` **does** matter, however ordering
    /// for record data does **not** matter, as long as all defined members are present.
    pub fn matches_record(&self, record: &Record<N, Plaintext<N>>, record_name: &Identifier<N>) -> Result<()> {
        self.matches_record_internal(record, record_name, 0)
    }

    /// Checks that the given plaintext matches the layout of the plaintext type.
    /// Note: Ordering does **not** matter, as long as all defined members are present.
    pub fn matches_plaintext(&self, plaintext: &Plaintext<N>, plaintext_type: &PlaintextType<N>) -> Result<()> {
        self.matches_plaintext_internal(plaintext, plaintext_type, 0)
    }
}

impl<N: Network> Stack<N> {
    /// Checks that the given value matches the layout of the value type.
    ///
    /// This method enforces `N::MAX_DATA_DEPTH` and `N::MAX_DATA_ENTRIES` limits.
    fn matches_value_internal(
        &self,
        value: &Value<N, Plaintext<N>>,
        value_type: &ValueType<N>,
        depth: usize,
    ) -> Result<()> {
        match (value, value_type) {
            (Value::Constant(plaintext), ValueType::Constant(plaintext_type))
            | (Value::Public(plaintext), ValueType::Public(plaintext_type))
            | (Value::Private(plaintext), ValueType::Private(plaintext_type)) => {
                self.matches_plaintext_internal(plaintext, plaintext_type, depth)
            }
            (Value::Record(record), ValueType::Record(record_name)) => {
                self.matches_record_internal(record, record_name, depth)
            }
            _ => bail!("Invalid value: function expected '{value_type}'"),
        }
    }

    /// Checks that the given record matches the layout of the record type.
    /// Note: Ordering for `owner` and `balance` **does** matter, however ordering
    /// for record data does **not** matter, as long as all defined members are present.
    ///
    /// This method enforces `N::MAX_DATA_DEPTH` and `N::MAX_DATA_ENTRIES` limits.
    fn matches_record_internal(
        &self,
        record: &Record<N, Plaintext<N>>,
        record_name: &Identifier<N>,
        depth: usize,
    ) -> Result<()> {
        // If the depth exceeds the maximum depth, then the plaintext type is invalid.
        ensure!(depth <= N::MAX_DATA_DEPTH, "Plaintext exceeded maximum depth of {}", N::MAX_DATA_DEPTH);

        // Ensure the record name is valid.
        ensure!(!self.program.is_reserved_name(record_name), "Record name '{record_name}' is reserved");

        // Retrieve the record type from the program.
        let record_type = match self.program.get_record(record_name) {
            Ok(record_type) => record_type,
            Err(..) => bail!("Record '{record_name}' is not defined in the program"),
        };

        // Ensure the record name matches.
        if record_type.name() != record_name {
            bail!("Expected record '{record_name}', found record '{}'", record_type.name())
        }

        // Ensure the number of record members does not exceed the maximum.
        let num_members = record.data().len();
        ensure!(num_members <= N::MAX_DATA_ENTRIES, "'{record_name}' cannot exceed {} entries", N::MAX_DATA_ENTRIES);

        // Ensure the number of interface members match.
        let num_expected_members = record_type.entries().len();
        if num_expected_members != num_members {
            bail!("'{record_name}' expected {num_expected_members} members, found {num_members} members")
        }

        // TODO (howardwu): Check that the record owner and balance visibility matches.

        // Ensure the record data matches the defined type.
        // Note: Ordering does **not** matter, as long as all defined members are present.
        for (expected_name, expected_type) in record_type.entries() {
            match record.data().iter().find(|(name, _)| *name == expected_name) {
                // Ensure the member type matches.
                Some((member_name, member_value)) => {
                    // Ensure the member name is valid.
                    ensure!(!self.program.is_reserved_name(member_name), "Member name '{member_name}' is reserved");
                    // Ensure the member value matches (recursive call).
                    self.matches_value_internal(member_value, expected_type, depth + 1)?
                }
                None => bail!("'{record_name}' is missing member '{expected_name}'",),
            }
        }
        Ok(())
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
                            self.matches_plaintext_internal(member_plaintext, expected_type, depth + 1)?
                        }
                        None => bail!("'{interface_name}' is missing member '{expected_name}'",),
                    }
                }
                Ok(())
            }
        }
    }
}
