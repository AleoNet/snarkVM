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

#[cfg(test)]
use snarkvm_circuits_types::environment::assert_scope;

use snarkvm_circuits_types::{environment::prelude::*, Address, Boolean, I64};

// TODO (howardwu): Check mode is only public/private, not constant.
pub struct Record<E: Environment> {
    owner: Address<E>,
    value: I64<E>,
    data: Vec<Box<dyn DataType<Boolean<E>>>>,
    // program_id: Vec<Boolean<E>>,
    // randomizer: BaseField<E>,
    // record_view_key: BaseField<E>,
}

impl<E: Environment> Record<E> {
    /// Returns the record owner.
    pub fn owner(&self) -> &Address<E> {
        &self.owner
    }

    /// Returns the record value.
    pub fn value(&self) -> &I64<E> {
        &self.value
    }

    /// Returns the record data.
    pub fn data(&self) -> &Vec<Box<dyn DataType<Boolean<E>>>> {
        &self.data
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_types::{environment::Circuit, Field, Group};

    #[test]
    fn test_record_data() {
        let first = Field::<Circuit>::from_str("10field.public");
        let second = Boolean::from_str("true.private");
        let third = I64::from_str("99i64.public");

        let _candidate = Record {
            owner: Address::from(Group::from_str("2group.private")),
            value: I64::from_str("1i64.private"),
            data: vec![Box::new(first), Box::new(second), Box::new(third)],
        };
    }
}
