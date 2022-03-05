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

use crate::{Immediate, Memory, Opcode, Operand, Register};

/// Stores `operand` into `register`, if `destination` is not already set.
pub struct Store<M: Memory> {
    destination: Register<M::Environment>,
    operand: Operand<M>,
}

impl<M: Memory> Opcode for Store<M> {
    const NAME: &'static str = "store";

    fn evaluate(&self) {
        M::store(&self.destination, self.operand.to_value())
    }
}
