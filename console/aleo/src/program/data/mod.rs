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

use crate::{Value, ValueType};
use crate::{Address, Network, ViewKey};
use snarkvm_circuits_environment::Mode;
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{FromBits, ToBits};

use anyhow::{bail, Result};
use itertools::Itertools;

struct Literal<N: Network>(N::Field);
struct LiteralType<N: Network>(N::Field);

/// A value stored in program data.
pub struct Data<N: Network, Private: ValueType> {
    data: Vec<Value<N, Private>>
}

impl<N: Network, Private: ValueType> Data<N, Private> {
    /// Returns the data ID, as a hash over the **`Data<N, Ciphertext<N>>` variant**.
    pub fn to_id(&self) -> Result<N::Field> {
        N::hash_psd8([self.data])
    }
}
