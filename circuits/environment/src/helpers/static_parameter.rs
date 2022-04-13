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

// Sealed trait pattern for `StaticParameter`
pub(super) mod parameter {
    use crate::{Eject, Mode};

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

    impl<T: Eject> StaticParameter for CircuitOrMode<T> {}
    impl<T0: Eject, T1: Eject> StaticParameter for (CircuitOrMode<T0>, CircuitOrMode<T1>) {}
    impl<T0: Eject, T1: Eject, T2: Eject> StaticParameter for (CircuitOrMode<T0>, CircuitOrMode<T1>, CircuitOrMode<T2>) {}
    impl<T0: Eject, T1: Eject, T2: Eject, T3: Eject> StaticParameter
        for (CircuitOrMode<T0>, CircuitOrMode<T1>, CircuitOrMode<T2>, CircuitOrMode<T3>)
    {
    }
}
