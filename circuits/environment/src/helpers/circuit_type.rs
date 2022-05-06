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
#[derive(Debug, Clone)]
pub enum CircuitType<T: Eject> {
    Constant(Constant<T>),
    Public,
    Private,
}

impl<T: Eject> CircuitType<T> {
    pub fn mode(&self) -> Mode {
        match self {
            CircuitType::Constant(constant) => constant.eject_mode(),
            CircuitType::Public => Mode::Public,
            CircuitType::Private => Mode::Private,
        }
    }
}

/// Initializes a new `CircuitType` from a circuit.
/// If the circuit is constant, the `CircuitType` will be `Constant(circuit)`.
/// Otherwise, the `CircuitType` will be `Public` or `Private`.
impl<T: Eject + Clone> From<T> for CircuitType<T> {
    fn from(circuit: T) -> Self {
        match circuit.eject_mode() {
            Mode::Constant => CircuitType::Constant(Constant(circuit)),
            Mode::Public => CircuitType::Public,
            Mode::Private => CircuitType::Private,
        }
    }
}

/// Initializes a new `CircuitType` from a circuit.
/// If the circuit is constant, the `CircuitType` will be `Constant(circuit)`.
/// Otherwise, the `CircuitType` will be `Public` or `Private`.
impl<T: Eject + Clone> From<&T> for CircuitType<T> {
    fn from(circuit: &T) -> Self {
        match circuit.eject_mode() {
            Mode::Constant => CircuitType::Constant(Constant(circuit.clone())),
            Mode::Public => CircuitType::Public,
            Mode::Private => CircuitType::Private,
        }
    }
}
