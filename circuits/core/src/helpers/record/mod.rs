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

// #[cfg(test)]
// use snarkvm_circuits_types::environment::assert_scope;

use crate::{Identifier, Literal, Value};
use snarkvm_circuits_types::{environment::prelude::*, Address, I64};

// TODO (howardwu): Check mode is only public/private, not constant.
#[derive(Debug, Clone)]
pub struct Record<E: Environment> {
    name: Identifier<E>,
    owner: Address<E>,
    value: I64<E>,
    data: Vec<Value<E>>,
    // program_id: Vec<Boolean<E>>,
    // randomizer: BaseField<E>,
    // record_view_key: BaseField<E>,
}

impl<E: Environment> Record<E> {
    /// Returns the name of the record.
    pub fn name(&self) -> &Identifier<E> {
        &self.name
    }

    /// Returns the members of the record.
    pub fn members(&self) -> Vec<Value<E>> {
        [Value::Literal(Literal::Address(self.owner.clone())), Value::Literal(Literal::I64(self.value.clone()))]
            .into_iter()
            .chain(self.data.iter().cloned())
            .collect::<Vec<_>>()
    }

    /// Returns the record owner.
    pub fn owner(&self) -> &Address<E> {
        &self.owner
    }

    /// Returns the record value.
    pub fn value(&self) -> &I64<E> {
        &self.value
    }

    /// Returns the record data.
    pub fn data(&self) -> &Vec<Value<E>> {
        &self.data
    }
}

impl<E: Environment> TypeName for Record<E> {
    fn type_name() -> &'static str {
        "record"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_types::{environment::Circuit, Group};

    #[test]
    fn test_record() {
        let first = Value::Literal(Literal::<Circuit>::from_str("10field.public"));
        let second = Value::Literal(Literal::from_str("true.private"));
        let third = Value::Literal(Literal::from_str("99i64.public"));

        let _candidate = Record {
            name: Identifier::from_str("foo"),
            owner: Address::from(Group::from_str("2group.private")),
            value: I64::from_str("1i64.private"),
            data: vec![first, second, third],
        };
    }
}
