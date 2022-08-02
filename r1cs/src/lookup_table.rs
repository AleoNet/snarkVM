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

use snarkvm_fields::Field;
use snarkvm_utilities::serialize::*;

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LookupTable<F: Field>(pub Vec<(F, F, F)>);

impl<F: Field> Default for LookupTable<F> {
    fn default() -> Self {
        Self(vec![])
    }
}

impl<F: Field> LookupTable<F> {
    pub fn fill(&mut self, val_1: F, val_2: F, val_3: F) {
        self.0.push((val_1, val_2, val_3))
    }
}
