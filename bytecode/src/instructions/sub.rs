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

/// Subtracts `first` from `second`, storing the outcome in `destination`.
pub struct Sub<M: Memory> {
    destination: Register<M::Environment>,
    first: Operand<M>,
    second: Operand<M>,
}

impl<M: Memory> Opcode for Sub<M> {
    const NAME: &'static str = "sub";

    fn evaluate(&self) {
        match (self.first.to_value(), self.second.to_value()) {
            (Immediate::BaseField(a), Immediate::BaseField(b)) => {
                M::store(&self.destination, Immediate::BaseField(a - b))
            }
            (Immediate::Group(a), Immediate::Group(b)) => M::store(&self.destination, Immediate::Group(a - b)),
            _ => M::halt(format!("Invalid {} instruction", Self::NAME)),
        }
    }
}
