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

/// Wrapper struct for circuits whose mode is constant.
#[derive(Debug, Clone)]
pub struct Constant<T: Eject>(T);

impl<T: Eject> Constant<T> {
    /// Initializes a new `Constant`. Ensures that `Constant` cannot be initialized if the input circuit is not constant.
    pub fn new(circuit: T) -> Self {
        assert!(circuit.eject_mode().is_constant());
        Self(circuit)
    }
}

impl<T: Eject> Eject for Constant<T> {
    type Primitive = T::Primitive;

    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    fn eject_value(&self) -> Self::Primitive {
        self.0.eject_value()
    }
}

/// Helper enum used in the case where a circuit's output mode or counts are determined by
/// its mode and the actual value of the circuit.
/// See Boolean::nor, where exactly one of the operands is a constant, for an example.
#[derive(Debug, Clone)]
pub enum ConstantOrMode<T: Eject> {
    Constant(Constant<T>),
    Mode(Mode),
}

impl<T: Eject> ConstantOrMode<T> {
    pub fn mode(&self) -> Mode {
        match self {
            ConstantOrMode::Constant(constant) => constant.eject_mode(),
            ConstantOrMode::Mode(mode) => *mode,
        }
    }
}

/// Initializes a new `ModeOrConstant` from a circuit.
/// If the circuit is constant, the `ModeOrConstant` will be a `Constant`.
/// Otherwise, the `ModeOrConstant` will be a `Mode`.
impl<T: Eject> From<T> for ConstantOrMode<T> {
    fn from(circuit: T) -> Self {
        match circuit.eject_mode() {
            Mode::Constant => ConstantOrMode::Constant(Constant(circuit)),
            _ => ConstantOrMode::Mode(circuit.eject_mode()),
        }
    }
}
