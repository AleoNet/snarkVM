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

use crate::{Eject, Mode};

/// Helper enum used in the case where a circuit's output mode or counts are determined by
/// its mode and the actual value of the circuit.
/// See Boolean::nor, where exactly one of the operands is a constant, for an example.
pub enum CircuitOrMode<T: Eject> {
    Circuit(T),
    Mode(Mode),
}

impl<T: Eject> CircuitOrMode<T> {
    pub fn mode(&self) -> Mode {
        match self {
            CircuitOrMode::Circuit(circuit) => circuit.eject_mode(),
            CircuitOrMode::Mode(mode) => *mode,
        }
    }

    pub fn is_constant(&self) -> bool {
        self.mode().is_constant()
    }

    pub fn is_circuit(&self) -> bool {
        match self {
            CircuitOrMode::Circuit(_) => true,
            CircuitOrMode::Mode(_) => false,
        }
    }

    pub fn is_mode(&self) -> bool {
        match self {
            CircuitOrMode::Circuit(_) => false,
            CircuitOrMode::Mode(_) => true,
        }
    }
}

pub trait StaticParameter {}

// Implement StaticParameter for commonly used type.
impl StaticParameter for () {}
impl StaticParameter for Mode {}
impl<T: Eject> StaticParameter for CircuitOrMode<T> {}

// Implement StaticParameter for composite types.
impl<T: StaticParameter> StaticParameter for Vec<T> {}
impl<T: StaticParameter> StaticParameter for &[T] {}

impl<P0: StaticParameter, P1: StaticParameter> StaticParameter for (P0, P1) {}
impl<P0: StaticParameter, P1: StaticParameter, P2: StaticParameter> StaticParameter for (P0, P1, P2) {}
impl<P0: StaticParameter, P1: StaticParameter, P2: StaticParameter, P3: StaticParameter> StaticParameter
    for (P0, P1, P2, P3)
{
}
