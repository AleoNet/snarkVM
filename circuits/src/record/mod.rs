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

use crate::{Address, BaseField, Boolean, Environment, I64};

// #[derive(Clone, Debug)]
pub struct Record<E: Environment> {
    owner: Address<E>,
    value: I64<E>,
    payload: Vec<Boolean<E>>,
    program_id: Vec<Boolean<E>>,
    randomizer: BaseField<E>,
    record_view_key: BaseField<E>,
}

// impl<E: Environment> Record<E> {
//     ///
//     /// Initializes a new instance of a record.
//     ///
//     pub fn new(value: Affine<E>) -> Self {
//         Self(value)
//     }
// }

impl<E: Environment> AsRef<Record<E>> for Record<E> {
    fn as_ref(&self) -> &Record<E> {
        &self
    }
}
